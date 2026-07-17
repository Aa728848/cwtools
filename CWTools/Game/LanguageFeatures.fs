namespace CWTools.Games

open System
open System.Collections.Concurrent
open CWTools.Utilities.Position
open System.IO
open Files
open CWTools.Utilities.Utils
open CWTools.Process
open CWTools.Rules
open CWTools.Common
open CWTools.Parser

module LanguageFeatures =

    let private completionEntityCache = ConcurrentDictionary<string, struct (int * Entity)>()
    let private infoEntityCache = ConcurrentDictionary<string, struct (int * Entity)>()

    let private typeReferenceIndexCache =
        ConcurrentDictionary<struct (int * int), Map<string * string, range list>>()

    let clearCompletionEntityCache () =
        completionEntityCache.Clear()
        infoEntityCache.Clear()

    let clearTypeReferenceIndexCache () =
        typeReferenceIndexCache.Clear()

    let private scriptedEffectParamMapCache =
        ConcurrentDictionary<string, struct (obj * Map<string, string list>)>()

    let private buildScriptedEffectParamMap (e: Entity) : Map<string, string list> =
        let addNodes (root: Node) (acc: Map<string, string list>) =
            root.Children
            |> List.fold (fun (m: Map<string, string list>) (n: Node) ->
                match Compute.Jomini.getScriptedEffectParams n with
                | [] -> m
                | ps ->
                    let key = n.Key.ToLowerInvariant()
                    let prev = Map.tryFind key m |> Option.defaultValue []
                    Map.add key (prev @ ps |> List.distinct) m) acc
        let raw = addNodes e.rawEntity Map.empty
        if System.Object.ReferenceEquals(e.entity, e.rawEntity) then raw
        else addNodes e.entity raw

    let private entityScriptedParamMap (e: Entity) (lazyObj: obj) : Map<string, string list> =
        match scriptedEffectParamMapCache.TryGetValue e.filepath with
        | true, struct (cached, m) when System.Object.ReferenceEquals(cached, lazyObj) -> m
        | _ ->
            let m = buildScriptedEffectParamMap e
            scriptedEffectParamMapCache.[e.filepath] <- struct (lazyObj, m)
            m

    let private isSameText (left: string) (right: string) =
        String.Equals(left, right, StringComparison.Ordinal)

    let private trimReferenceValue (value: string) =
        if isNull value then "" else value.Trim().Trim('"')

    let private addRangeToIndex key position (index: Map<string * string, range list>) =
        let existing = index |> Map.tryFind key |> Option.defaultValue []
        index |> Map.add key (position :: existing)

    let private buildTypeReferenceIndex
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        =
        let referenceData (e: Entity) (lazyData: Lazy<#ComputedData>) : Map<string, ReferenceDetails list> =
            let referencedTypes = lazyData.Force().Referencedtypes

            if referencedTypes.IsSome then
                referencedTypes.Value
            else
                match infoService with
                | Some info ->
                    info.GetReferencedTypes e
                    |> Seq.map (fun kvp -> kvp.Key, kvp.Value |> Seq.toList)
                    |> Map.ofSeq
                | None -> Map.empty

        resourceManager.Api.ValidatableEntities()
        |> Seq.collect (fun struct (e, lazyData) ->
            referenceData e lazyData
            |> Map.toSeq
            |> Seq.collect (fun (typeName, refs) ->
                let baseTypeName = typeName.Split('.').[0]
                refs
                |> Seq.choose (fun ref ->
                    match ref.referenceType with
                    | ReferenceType.TypeDef
                    | ReferenceType.TypeDefFuzzy ->
                        let value = ref.name.GetString()
                        if String.IsNullOrWhiteSpace value then None
                        else Some((baseTypeName, value), ref.position)
                    | _ -> None)))
        |> Seq.fold (fun index (key, position) -> addRangeToIndex key position index) Map.empty
        |> Map.map (fun _ positions -> positions |> List.rev)

    let getOrBuildTypeReferenceIndex
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        =
        let managerId = System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(resourceManager)
        let version = ResourceManagerEager.currentVersion ()
        let cacheKey = struct (managerId, version)

        let index =
            typeReferenceIndexCache.GetOrAdd(
                cacheKey,
                fun _ ->
                    if typeReferenceIndexCache.Count > 4 then
                        for key in typeReferenceIndexCache.Keys |> Seq.toArray do
                            let struct (cachedManagerId, cachedVersion) = key
                            if cachedManagerId = managerId && cachedVersion <> version then
                                typeReferenceIndexCache.TryRemove(key) |> ignore

                    buildTypeReferenceIndex resourceManager infoService
            )

        index

    let getNodeForTypeDefAndType
        (resourceManager: ResourceManager<_>)
        (lookup: Lookup)
        (typedef: TypeDefinition)
        (typename: string)
        =
        let findNode (pos: range) (startNode: Node) =
            let rec findChild (node: Node) =
                if node.Position.Equals pos then
                    Some node
                else
                    match node.Nodes |> Seq.tryFind (fun n -> rangeContainsRange n.Position pos) with
                    | Some c -> findChild c
                    | None -> None

            findChild startNode

        lookup.typeDefInfo.TryFind typedef.name
        |> Option.bind (Array.tryFind (fun tdi -> tdi.id = typename))
        |> Option.bind (fun typeDefInfoForTypeName ->
            resourceManager.Api.GetEntityByFilePath typeDefInfoForTypeName.range.FileName
            |> Option.bind (fun struct (e, _) -> findNode typeDefInfoForTypeName.range e.entity))

    let makeEntityResourceInput (fileManager: FileManager) filepath filetext =
        let filepath = Path.GetFullPath(filepath)
        let logicalpath = fileManager.ConvertPathToLogicalPath filepath
        let scope = fileManager.GetScopeForPath filepath |> Option.defaultValue "unknown"

        EntityResourceInput
            { scope = scope
              filepath = filepath
              logicalpath = logicalpath
              filetext = filetext
              validate = true }

    /// Parse a file into an Entity, reusing the cached result when the content
    /// hash is unchanged. Used by the hover / goto / scopes paths to avoid
    /// re-parsing the whole file on every request (and twice per hover).
    let private processResourceCachedInfo
        (resourceManager: ResourceManager<_>)
        (fileManager: FileManager)
        (filepath: string)
        (filetext: string)
        =
        let hash = filetext.GetHashCode()
        match infoEntityCache.TryGetValue(filepath) with
        | true, struct (cachedHash, cachedEntity) when cachedHash = hash -> Some cachedEntity
        | _ ->
            match resourceManager.ManualProcessResource (makeEntityResourceInput fileManager filepath filetext) with
            | Some e ->
                infoEntityCache.[filepath] <- struct (hash, e)
                Some e
            | None -> None

    let makeFileWithContentResourceInput (fileManager: FileManager) filepath filetext =
        let filepath = Path.GetFullPath(filepath)
        let logicalpath = fileManager.ConvertPathToLogicalPath filepath
        let scope = fileManager.GetScopeForPath filepath |> Option.defaultValue "unknown"

        FileWithContentResourceInput
            { scope = scope
              filepath = filepath
              logicalpath = logicalpath
              filetext = filetext
              validate = true }


    let private isCompletionKeyChar c =
        Char.IsLetterOrDigit c
        || c = '_'
        || c = '.'
        || c = ':'
        || c = '@'
        || c = '-'
        || c = '?'
        || c = magicChar

    let private commentStartOutsideQuotes (line: string) =
        let mutable quote = false
        let mutable escaped = false
        let mutable result = -1
        let mutable i = 0
        while result < 0 && i < line.Length do
            let c = line.[i]
            if escaped then
                escaped <- false
            elif c = '\\' && quote then
                escaped <- true
            elif c = '"' then
                quote <- not quote
            elif c = '#' && not quote then
                result <- i
            i <- i + 1
        result

    let private braceDepthBeforeCursor (split: string array) currentLineIdx column =
        let mutable depth = 0
        let mutable quote = false
        let mutable escaped = false

        for lineIdx = 0 to currentLineIdx do
            if lineIdx >= 0 && lineIdx < split.Length then
                let line = split.[lineIdx]
                let limit =
                    if lineIdx = currentLineIdx then min column line.Length else line.Length
                let mutable i = 0
                let mutable stopped = false
                while i < limit && not stopped do
                    let c = line.[i]
                    if escaped then
                        escaped <- false
                    elif c = '\\' && quote then
                        escaped <- true
                    elif c = '"' then
                        quote <- not quote
                    elif c = '#' && not quote then
                        stopped <- true
                    elif not quote then
                        match c with
                        | '{' -> depth <- depth + 1
                        | '}' -> depth <- max 0 (depth - 1)
                        | _ -> ()
                    i <- i + 1

        depth

    let private tryRepairIncompleteLhsCompletionText
        (split: string array)
        (filetextWithMagic: string)
        currentLineIdx
        (pos: pos)
        =
        if currentLineIdx < 0 || currentLineIdx >= split.Length then None
        else
            let originalLine = split.[currentLineIdx]
            let column = min pos.Column originalLine.Length
            let commentStart = commentStartOutsideQuotes originalLine
            let beforeCursor = originalLine.Substring(0, column)
            let afterCursor = originalLine.Substring(column)
            let afterCursorBeforeComment =
                if commentStart >= column then
                    originalLine.Substring(column, commentStart - column)
                elif commentStart < 0 then
                    afterCursor
                else
                    ""

            let isCommentLine = originalLine.TrimStart().StartsWith("#")
            let hasEqualsBeforeCursor = beforeCursor.Contains("=")
            let hasEqualsAfterCursor = afterCursorBeforeComment.Contains("=")
            let inBlock = braceDepthBeforeCursor split currentLineIdx column > 0

            if isCommentLine || hasEqualsBeforeCursor || hasEqualsAfterCursor || not inBlock then
                None
            else
                let linesWithMagic = filetextWithMagic.Split('\n')
                if currentLineIdx >= linesWithMagic.Length then None
                else
                    let lineWithMagic = linesWithMagic.[currentLineIdx]
                    let magicIndex =
                        if column < lineWithMagic.Length && lineWithMagic.[column] = magicChar then
                            column
                        else
                            lineWithMagic.IndexOf(magicChar)

                    if magicIndex < 0 then None
                    else
                        let mutable tokenStart = magicIndex
                        while tokenStart > 0 && isCompletionKeyChar lineWithMagic.[tokenStart - 1] do
                            tokenStart <- tokenStart - 1

                        let mutable tokenEnd = magicIndex + 1
                        while tokenEnd < lineWithMagic.Length && isCompletionKeyChar lineWithMagic.[tokenEnd] do
                            tokenEnd <- tokenEnd + 1

                        let lineForRepair, tokenEnd =
                            if tokenStart = magicIndex && tokenEnd = magicIndex + 1 then
                                lineWithMagic.Insert(magicIndex, "x"), tokenEnd + 1
                            else
                                lineWithMagic, tokenEnd

                        let repairedLine = lineForRepair.Insert(tokenEnd, " = { }")
                        linesWithMagic.[currentLineIdx] <- repairedLine
                        Some(String.concat "\n" linesWithMagic)

    let private scriptCompletion
        (fileManager: FileManager)
        (completionService: CompletionService option)
        (infoService: InfoService option)
        (resourceManager: ResourceManager<_>)
        (pos: pos)
        (filepath: string)
        (filetext: string)
        =
        let split = filetext.Split('\n')

        // 获取当前行（注意 pos.Line 是 1-based）
        let currentLineIdx = pos.Line - 1
        let currentLine = if currentLineIdx >= 0 && currentLineIdx < split.Length then split.[currentLineIdx] else ""

        let filetext =
            split
            |> Array.mapi (fun i s ->
                if i = currentLineIdx then
                    log (sprintf "%s" s)
                    let s = s.Insert(pos.Column, magicCharString) in
                    log (sprintf "%s" s)
                    s
                else
                    s)
            |> String.concat "\n"

        // Use cached Entity when file content hasn't changed to avoid expensive re-parsing.
        // The filetext here already has the magic char inserted at cursor position,
        // so we hash the modified text (it changes on every cursor move, but stays
        // stable for TriggerForIncompleteCompletions re-requests at the same position).
        let processResourceTextCached (text: string) =
            let contentHash = text.GetHashCode()
            let resource = lazy (makeEntityResourceInput fileManager filepath text)
            match completionEntityCache.TryGetValue(filepath) with
            | true, struct (cachedHash, cachedEntity) when cachedHash = contentHash ->
                Some cachedEntity
            | _ ->
                match resourceManager.ManualProcessResource resource.Value with
                | Some e ->
                    completionEntityCache.[filepath] <- struct (contentHash, e)
                    Some e
                | None -> None

        let processResourceCached () =
            processResourceTextCached filetext

        let processRepairedResourceCached () =
            tryRepairIncompleteLhsCompletionText split filetext currentLineIdx pos
            |> Option.bind processResourceTextCached

        // 检测当前文件是否是 inline_script 文件
        let isInlineScriptFile =
            filepath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
            filepath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase)

        let inlinePathDefaultPattern =
            System.Text.RegularExpressions.Regex(@"\$[A-Za-z_][A-Za-z0-9_]*\|[^$]*\$")

        let inlinePathParameterPattern allowPathDefaults =
            if allowPathDefaults then
                System.Text.RegularExpressions.Regex(@"\$[A-Za-z_][A-Za-z0-9_]*(?:\|[^$]*)?\$")
            else
                System.Text.RegularExpressions.Regex(@"\$[A-Za-z_][A-Za-z0-9_]*\$")

        let canMatchParameterizedInlinePath allowPathDefaults (path: string) =
            allowPathDefaults || not (inlinePathDefaultPattern.IsMatch path)

        // 特殊处理：@[ expression ] 内部的 scripted_variable 补全
        let tryExpressionCompletion () =
            if currentLineIdx >= 0 && currentLineIdx < split.Length then
                let line = split.[currentLineIdx]
                let col = pos.Column

                // 检查光标是否在 @[...] 表达式内部
                let textBeforeCursor = if col <= line.Length then line.Substring(0, col) else line
                let textAfterCursor = if col < line.Length then line.Substring(col) else ""

                // 查找最近的 @[ 和 ]
                let lastOpenBracket = textBeforeCursor.LastIndexOf("@[")
                let lastCloseBracket = textBeforeCursor.LastIndexOf("]")
                let nextCloseBracket = textAfterCursor.IndexOf("]")

                // 如果在 @[...] 内部（最近的 @[ 在最近的 ] 之后，且后面还有 ]）
                if lastOpenBracket >= 0 && lastOpenBracket > lastCloseBracket && nextCloseBracket >= 0 then
                    log (sprintf "tryExpressionCompletion: inside @[ expression ]")

                    // 提取表达式内容
                    let exprStart = lastOpenBracket + 2
                    let exprContent = textBeforeCursor.Substring(exprStart)

                    // 检查当前是否在输入变量名
                    // 在表达式内部，变量名没有 @ 前缀，直接是 wsg_armor_add 这样的形式
                    // 匹配模式：操作符或空格后的标识符，或者表达式开头的标识符
                    let varPattern = System.Text.RegularExpressions.Regex(@"(?:^|[\s\+\-\*/\(])\s*([A-Za-z_][A-Za-z0-9_$]*)$")
                    let varMatch = varPattern.Match(exprContent)

                    // 如果正在输入变量名，或者刚输入了操作符/空格
                    if varMatch.Success || System.Text.RegularExpressions.Regex(@"[\s\+\-\*/\(\[]$").IsMatch(exprContent) then
                        log (sprintf "tryExpressionCompletion: completing scripted_variable (match: %b, content: '%s')" varMatch.Success exprContent)

                        // 获取所有 scripted_variables
                        let allEntities = resourceManager.Api.AllEntities()
                        let scriptedVars =
                            allEntities
                            |> Seq.filter (fun struct (e, _) ->
                                e.filepath.Contains("common/scripted_variables") ||
                                e.filepath.Contains("common\\scripted_variables") ||
                                e.logicalpath.Contains("common/scripted_variables") ||
                                e.logicalpath.Contains("common\\scripted_variables"))
                            |> Seq.collect (fun struct (e, _) ->
                                try
                                    CWTools.Validation.Stellaris.STLValidation.getDefinedVariables e.entity
                                with _ -> [])
                            |> Seq.filter (fun varName -> not (varName.StartsWith("@[")) && not (varName.StartsWith(@"@\["))) // 过滤掉表达式
                            |> Seq.distinct
                            |> Seq.toArray

                        if scriptedVars.Length > 0 then
                            let completionItems =
                                scriptedVars
                                // 移除 @ 前缀，因为表达式内部变量名不需要 @
                                |> Array.map (fun varName ->
                                    let displayName = if varName.StartsWith("@") then varName.Substring(1) else varName
                                    CompletionResponse.Detailed(
                                        displayName,
                                        Some($"Scripted variable: {varName}"),
                                        None,
                                        CompletionCategory.Variable))
                                |> Array.toList
                            Some completionItems
                        else
                            None
                    else
                        None
                else
                    None
            else
                None

        // special handling: inline_script completion
        let tryInlineScriptCompletion () =
            if currentLineIdx >= 0 && currentLineIdx < split.Length then
                let line = split.[currentLineIdx]
                let trimmedLine = line.TrimStart()

                log (sprintf "tryInlineScriptCompletion: lineIdx=%d, line='%s'" currentLineIdx line)

                if trimmedLine.StartsWith("#") then
                    log "tryInlineScriptCompletion: skipping comment line"
                    None
                else
                    let col = pos.Column
                    let searchEnd = min col line.Length
                    let textBeforeCursor =
                        if searchEnd > 0 && searchEnd <= line.Length then line.Substring(0, searchEnd)
                        else ""

                    log (sprintf "tryInlineScriptCompletion: col=%d, searchEnd=%d, textBeforeCursor='%s'" col searchEnd textBeforeCursor)

                    // Check for no-brace form: inline_script = path
                    // e.g. "inline_script = comp|" or "inline_script = |"
                    let inlineDirectPattern = System.Text.RegularExpressions.Regex(@"^\s*inline_script\s*=\s*([^{}\s]*)$")
                    let inlineDirectMatch = inlineDirectPattern.Match(textBeforeCursor)
                    if inlineDirectMatch.Success then
                        log (sprintf "tryInlineScriptCompletion: direct form 'inline_script = path', prefix='%s'" inlineDirectMatch.Groups.[1].Value)
                        let allEntities = resourceManager.Api.AllEntities()
                        let inlineScriptEntities =
                            allEntities
                            |> Seq.filter (fun struct (e, _) ->
                                e.logicalpath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
                                e.logicalpath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase))
                            |> Seq.toArray
                        let extractScriptRelPath (logicalpath: string) =
                            let pathLower = logicalpath.ToLowerInvariant()
                            let inlineIdx =
                                let idx1 = pathLower.IndexOf("common/inline_scripts/")
                                let idx2 = pathLower.IndexOf("common\\inline_scripts\\")
                                if idx1 >= 0 then idx1 + "common/inline_scripts/".Length
                                elif idx2 >= 0 then idx2 + "common\\inline_scripts\\".Length
                                else -1
                            if inlineIdx >= 0 && inlineIdx < logicalpath.Length then
                                Some(logicalpath.Substring(inlineIdx).Replace(".txt", ""))
                            else None
                        let inlineScriptPaths =
                            inlineScriptEntities
                            |> Array.choose (fun struct (e, _) -> extractScriptRelPath e.logicalpath)
                            |> Array.distinct
                        let completionItems =
                            inlineScriptPaths
                            |> Array.map (fun name ->
                                CompletionResponse.Detailed(
                                    name,
                                    Some(sprintf "Inline script: %s" name),
                                    None,
                                    CompletionCategory.Link))
                            |> Array.toList
                        Some completionItems
                    else

                    let rec findInlineScriptContext lineIdx braceDepth maxDepth =
                        if lineIdx < 0 then
                            None
                        else
                            let l = split.[lineIdx].Trim()
                            let openBraces = l.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                            let closeBraces = l.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                            let braceDelta = openBraces - closeBraces
                            // Going upward: { increases depth (exiting a block opening),
                            // } decreases depth (entering a block closing).
                            // For cursor to be DIRECTLY inside inline_script's block:
                            //   1. The inline_script line must open a block (braceDelta > 0)
                            //   2. braceDepth must be 0 (no unmatched { between cursor and here)
                            //   3. maxDepth must be 0: depth never went above 0, meaning we never
                            //      crossed through any { on the way up. If we did (e.g. on_hit = {),
                            //      and then a } brought it back to 0, the cursor is in a sibling block,
                            //      NOT inside inline_script.
                            if (l.StartsWith("inline_script") || l.Contains("inline_script =")) && braceDelta > 0 && braceDepth = 0 && maxDepth = 0 then
                                Some lineIdx
                            else
                                let newDepth = braceDepth + braceDelta
                                let newMaxDepth = max maxDepth newDepth
                                if newDepth < -50 then None
                                else findInlineScriptContext (lineIdx - 1) newDepth newMaxDepth

                    let singleLineInlineIdx =
                        let openIdx = line.IndexOf('{')
                        if trimmedLine.StartsWith("inline_script") && openIdx >= 0 && col > openIdx then
                            let upToCursor = line.Substring(0, min col line.Length)
                            let opens = upToCursor |> Seq.filter (fun c -> c = '{') |> Seq.length
                            let closes = upToCursor |> Seq.filter (fun c -> c = '}') |> Seq.length
                            if opens - closes > 0 then Some currentLineIdx else None
                        else None

                    let inlineContext =
                        match singleLineInlineIdx with
                        | Some _ -> singleLineInlineIdx
                        | None -> findInlineScriptContext currentLineIdx 0 0

                    match inlineContext with
                    | Some inlineScriptLineIdx ->
                        // Confirmed inside inline_script block.
                        // ALL paths MUST return Some to block wrong regular completion.

                        let extractParamsFromFile (filepath: string) =
                            try
                                let fileContent = System.IO.File.ReadAllText(filepath)
                                let regex = System.Text.RegularExpressions.Regex(@"\$([A-Za-z_][A-Za-z0-9_]*)\$")
                                let matches = regex.Matches(fileContent)
                                [ for m in matches -> m.Groups.[1].Value ] |> List.distinct
                            with _ -> []

                        let extractScriptRelPath (logicalpath: string) =
                            let pathLower = logicalpath.ToLowerInvariant()
                            let inlineIdx =
                                let idx1 = pathLower.IndexOf("common/inline_scripts/")
                                let idx2 = pathLower.IndexOf("common\\inline_scripts\\")
                                if idx1 >= 0 then idx1 + "common/inline_scripts/".Length
                                elif idx2 >= 0 then idx2 + "common\\inline_scripts\\".Length
                                else -1
                            if inlineIdx >= 0 && inlineIdx < logicalpath.Length then
                                Some(logicalpath.Substring(inlineIdx).Replace(".txt", ""))
                            else
                                None

                        let allEntities = resourceManager.Api.AllEntities()
                        let inlineScriptEntities =
                            allEntities
                            |> Seq.filter (fun struct (e, _) ->
                                e.logicalpath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
                                e.logicalpath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase))
                            |> Seq.toArray

                        // 1. Check if on script = | line (script path completion)
                        let currentLineTrimmed = split.[currentLineIdx].Trim()
                        let isOnScriptLine =
                            let scriptLinePattern = System.Text.RegularExpressions.Regex(@"^\s*script\s*=")
                            scriptLinePattern.IsMatch(split.[currentLineIdx]) &&
                            not (currentLineTrimmed.StartsWith("inline_script"))

                        let scriptNamePatternSingleLine = System.Text.RegularExpressions.Regex(@"inline_script\s*=\s*\{[^}]*script\s*=\s*([^|\s]*)$")
                        let scriptNameMatchSingleLine = scriptNamePatternSingleLine.Match(textBeforeCursor)

                        if scriptNameMatchSingleLine.Success || isOnScriptLine then
                            log "tryInlineScriptCompletion: script name/path completion"
                            let inlineScriptPaths =
                                inlineScriptEntities
                                |> Array.choose (fun struct (e, _) -> extractScriptRelPath e.logicalpath)
                                |> Array.distinct
                            let completionItems =
                                inlineScriptPaths
                                |> Array.map (fun name ->
                                    CompletionResponse.Detailed(
                                        name,
                                        Some(sprintf "Inline script: %s" name),
                                        None,
                                        CompletionCategory.Link))
                                |> Array.toList
                            Some completionItems
                        else
                            // 2. Parameter completion: find script = xxx
                            // Search BOTH upward AND downward from cursor within the inline_script block
                            // to find the "script = xxx" line
                            let findScriptNameInBlock () =
                                let rec findBlockEnd lineIdx depth =
                                    if lineIdx >= split.Length then lineIdx - 1
                                    else
                                        let l = split.[lineIdx]
                                        let openBraces = l.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                                        let closeBraces = l.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                                        let newDepth = depth + openBraces - closeBraces
                                        if newDepth <= 0 then lineIdx
                                        else findBlockEnd (lineIdx + 1) newDepth
                                let blockEndLine = findBlockEnd inlineScriptLineIdx 0

                                let scriptPattern = System.Text.RegularExpressions.Regex(@"\bscript\s*=\s*([^\s}]+)")
                                let mutable result = None
                                for i in inlineScriptLineIdx .. blockEndLine do
                                    if result.IsNone && i >= 0 && i < split.Length then
                                        let m = scriptPattern.Match(split.[i])
                                        if m.Success then
                                            result <- Some (m.Groups.[1].Value)
                                result

                            match findScriptNameInBlock() with
                            | Some scriptName ->
                                log (sprintf "tryInlineScriptCompletion: found script='%s', looking up params" scriptName)

                                // Check if scriptName contains $PARAM$ (unresolved parameter in path)
                                let hasParamInPath = scriptName.Contains("$")

                                let scriptParams =
                                    if hasParamInPath && not (canMatchParameterizedInlinePath (not isInlineScriptFile) scriptName) then
                                        log "tryInlineScriptCompletion: inline_script path default is not valid inside inline_script files"
                                        []
                                    elif hasParamInPath then
                                        // Path contains parameters like "kuat_weapon_event/$INLINE$"
                                        // Extract the known prefix before the first $
                                        let dollarIdx = scriptName.IndexOf('$')
                                        let knownPrefix =
                                            if dollarIdx > 0 then scriptName.Substring(0, dollarIdx).Replace('\\', '/')
                                            else ""
                                        log (sprintf "tryInlineScriptCompletion: parameterized path, prefix='%s'" knownPrefix)

                                        // Find ALL scripts matching the prefix and collect union of params
                                        let allMatchingFiles =
                                            inlineScriptEntities
                                            |> Array.choose (fun struct (e, _) ->
                                                match extractScriptRelPath e.logicalpath with
                                                | Some relPath ->
                                                    let normRel = relPath.Replace('\\', '/')
                                                    if knownPrefix.Length > 0 && normRel.StartsWith(knownPrefix, StringComparison.OrdinalIgnoreCase) then
                                                        Some e.filepath
                                                    elif knownPrefix.Length = 0 then
                                                        Some e.filepath
                                                    else None
                                                | None -> None)

                                        log (sprintf "tryInlineScriptCompletion: found %d matching files for prefix '%s'" allMatchingFiles.Length knownPrefix)
                                        allMatchingFiles
                                        |> Array.collect (fun fp ->
                                            (extractParamsFromFile fp) |> List.toArray)
                                        |> Array.distinct
                                        |> Array.toList
                                    else
                                        // Exact path matching
                                        let matchingFilepath =
                                            inlineScriptEntities
                                            |> Array.tryPick (fun struct (e, _) ->
                                                match extractScriptRelPath e.logicalpath with
                                                | Some relPath ->
                                                    let normRel = relPath.Replace('\\', '/')
                                                    let normScript = scriptName.Replace('\\', '/')
                                                    if String.Equals(normRel, normScript, StringComparison.OrdinalIgnoreCase) ||
                                                       normRel.EndsWith("/" + normScript, StringComparison.OrdinalIgnoreCase) ||
                                                       normScript.EndsWith("/" + normRel, StringComparison.OrdinalIgnoreCase) then
                                                        Some e.filepath
                                                    else
                                                        None
                                                | None -> None)
                                        match matchingFilepath with
                                        | Some fp ->
                                            log (sprintf "tryInlineScriptCompletion: reading params from file '%s'" fp)
                                            extractParamsFromFile fp
                                        | None ->
                                            log (sprintf "tryInlineScriptCompletion: no matching file found for script '%s'" scriptName)
                                            []

                                log (sprintf "tryInlineScriptCompletion: found %d params: %A" scriptParams.Length scriptParams)

                                if scriptParams.Length > 0 then
                                    // Extract current word at cursor
                                    let currentWord =
                                        let lineText = split.[currentLineIdx]
                                        let cursorCol = min col lineText.Length
                                        if cursorCol > 0 then
                                            let mutable startIdx = cursorCol - 1
                                            while startIdx >= 0 && (System.Char.IsLetterOrDigit(lineText.[startIdx]) || lineText.[startIdx] = '_') do
                                                startIdx <- startIdx - 1
                                            startIdx <- startIdx + 1
                                            if startIdx < cursorCol then
                                                lineText.Substring(startIdx, cursorCol - startIdx)
                                            else ""
                                        else ""

                                    log (sprintf "tryInlineScriptCompletion: currentWord='%s'" currentWord)

                                    // Detect if cursor is in value position (right after `key =`).
                                    // Strip the in-progress identifier under the cursor and any
                                    // trailing spaces; if what remains ends with `=` the user is
                                    // typing a value (stay silent), otherwise a new parameter key.
                                    let isAfterEquals =
                                        let lineText = split.[currentLineIdx]
                                        let cursorCol = min col lineText.Length
                                        if cursorCol > 0 then
                                            let textBefore = lineText.Substring(0, cursorCol)
                                            let mutable e = textBefore.Length
                                            while e > 0 && (System.Char.IsLetterOrDigit(textBefore.[e - 1]) || textBefore.[e - 1] = '_') do
                                                e <- e - 1
                                            textBefore.Substring(0, e).TrimEnd().EndsWith("=")
                                        else false

                                    if isAfterEquals then
                                        log "tryInlineScriptCompletion: in value position, returning empty"
                                        Some []
                                    else
                                        let filteredParams =
                                            if currentWord.Length > 0 then
                                                scriptParams |> List.filter (fun p -> p.StartsWith(currentWord, StringComparison.OrdinalIgnoreCase))
                                            else
                                                scriptParams
                                        let completionItems =
                                            filteredParams
                                            |> List.mapi (fun i p ->
                                                CompletionResponse.Detailed(
                                                    p,
                                                    Some(sprintf "Parameter: %s" p),
                                                    Some (i + 1),
                                                    CompletionCategory.Variable))
                                        Some completionItems
                                else
                                    log "tryInlineScriptCompletion: no params found, returning empty"
                                    Some []

                            | None ->
                                // No script = xxx line found in the block
                                // Provide both "script" keyword AND available script paths
                                log "tryInlineScriptCompletion: no script line found, suggesting script keyword and paths"
                                let scriptKeyword =
                                    CompletionResponse.Snippet(
                                        "script",
                                        "script = $1",
                                        Some("script = <inline_script_path>"),
                                        Some 0,
                                        CompletionCategory.Other)
                                let scriptPaths =
                                    inlineScriptEntities
                                    |> Array.choose (fun struct (e, _) -> extractScriptRelPath e.logicalpath)
                                    |> Array.distinct
                                    |> Array.mapi (fun i name ->
                                        CompletionResponse.Snippet(
                                            sprintf "script = %s" name,
                                            sprintf "script = %s" name,
                                            Some(sprintf "Inline script: %s" name),
                                            Some (i + 1),
                                            CompletionCategory.Link))
                                    |> Array.toList
                                Some (scriptKeyword :: scriptPaths)

                    | None -> None
            else
                None


        // 特殊处理：value:script_value|param| 语法的参数补全
        let tryScriptValueCompletion () =
            // 先检查是否是注释行（以 # 开头的行）
            if currentLineIdx >= 0 && currentLineIdx < split.Length then
                let line = split.[currentLineIdx]
                let trimmedLine = line.TrimStart()
                
                // 如果是注释行，跳过 script_value 参数补全
                if trimmedLine.StartsWith("#") then
                    None
                else
                    let col = pos.Column
                    
                    // 检查是否是 value:name|param| 模式
                    // 情况1：已经存在 | 的情况 - value:xxx|
                    let searchEnd = min col line.Length
                    if searchEnd > 0 then
                        let textBeforeCursor =
                            if searchEnd <= line.Length then line.Substring(0, searchEnd)
                            else line

                        let scriptValueNameCompletions () =
                            let valuePrefixIdx =
                                textBeforeCursor.LastIndexOf("value:", StringComparison.OrdinalIgnoreCase)

                            if valuePrefixIdx < 0 then
                                None
                            else
                                let isTokenStart =
                                    if valuePrefixIdx = 0 then
                                        true
                                    else
                                        let c = textBeforeCursor.[valuePrefixIdx - 1]
                                        Char.IsWhiteSpace c
                                        || c = '='
                                        || c = '{'
                                        || c = '('
                                        || c = '"'
                                        || c = '\''

                                let suffix = textBeforeCursor.Substring(valuePrefixIdx + 6)

                                if not isTokenStart || suffix.IndexOf('|') >= 0 || suffix |> Seq.exists Char.IsWhiteSpace then
                                    None
                                else
                                    let names =
                                        resourceManager.Api.AllEntities()
                                        |> Seq.filter (fun struct (e, _) ->
                                            e.logicalpath.Contains("common/script_values", StringComparison.OrdinalIgnoreCase) ||
                                            e.logicalpath.Contains("common\\script_values", StringComparison.OrdinalIgnoreCase))
                                        |> Seq.collect (fun struct (e, _) -> e.entity.Children |> Seq.map _.Key)
                                        |> Seq.distinct
                                        |> Seq.sort
                                        |> Seq.toArray

                                    if names.Length = 0 then
                                        None
                                    else
                                        names
                                        |> Array.mapi (fun i name ->
                                            CompletionResponse.Simple(sprintf "value:%s" name, Some(i + 1), CompletionCategory.Value))
                                        |> Array.toList
                                        |> Some

                        let valuePattern = System.Text.RegularExpressions.Regex(@"value\s*:\s*([^|\s]+)\|")
                        let m = valuePattern.Match(line.Substring(0, searchEnd))

                        match scriptValueNameCompletions () with
                        | Some _ as completions -> completions
                        | None when m.Success ->
                            let scriptValueName = m.Groups.[1].Value

                            // 计算第一个 | 之后的位置
                            let pipeAfterValue = m.Index + m.Length
                            let remainingLen = col - pipeAfterValue

                            if remainingLen >= 0 then
                                let remainingText =
                                    if pipeAfterValue <= line.Length then
                                        line.Substring(pipeAfterValue, min remainingLen (line.Length - pipeAfterValue))
                                    else ""

                                // 检查是否在参数位置（偶数索引位置，0-based）
                                // value:name|param1|val1|param2|val2|
                                //             ^0    ^1   ^2   ^3
                                let pipeCount = remainingText.Split('|').Length - 1
                                let isParamPosition = pipeCount % 2 = 0

                                if isParamPosition then
                                    // 直接从所有实体中提取 script_value 参数
                                    // 不依赖预计算数据，而是实时提取
                                    let allParams =
                                        resourceManager.Api.AllEntities()
                                        |> Seq.filter (fun struct (e, _) ->
                                            e.logicalpath.Contains("common/script_values", StringComparison.OrdinalIgnoreCase) ||
                                            e.logicalpath.Contains("common\\script_values", StringComparison.OrdinalIgnoreCase))
                                        |> Seq.collect (fun struct (e, _) ->
                                            e.entity.Children
                                            |> Seq.filter (fun child -> child.Key.Equals(scriptValueName, StringComparison.OrdinalIgnoreCase))
                                            |> Seq.collect Compute.Jomini.getScriptValueParams)
                                        |> Seq.distinct
                                        |> Seq.toArray

                                    if allParams.Length > 0 then
                                        log (sprintf "ScriptValue completion params: %A" allParams)
                                        let completionItems =
                                            allParams
                                            |> Array.map (fun p ->
                                                // 设置 sortText 为一个极小值，使其排在列表最前面
                                                // 使用 CompletionCategory.Value
                                                CompletionResponse.Simple(p, None, CompletionCategory.Value))
                                            |> Array.toList
                                        log (sprintf "ScriptValue completion items count: %d" completionItems.Length)
                                        Some completionItems
                                    else
                                        None
                                else
                                    None
                            else
                                None
                        | None -> None
                    else
                        None
            else
                None

        // 特殊处理：scripted_effect / scripted_trigger 调用块内，按【被调用的那个具体定义】的
        // $PARAM$ 提供参数补全，而不是全局 enum[scripted_effect_params] 的全部参数。
        let tryScriptedEffectParamCompletion () =
            if currentLineIdx < 0 || currentLineIdx >= split.Length then None
            else
                let line = split.[currentLineIdx]
                if line.TrimStart().StartsWith("#") then None
                else
                    match processResourceCached () with
                    | None -> None
                    | Some entity ->
                        // 光标所在的最内层块节点，其 key 即被调用的 scripted_effect/trigger 名。
                        let rec deepestPath path (node: Node) =
                            match node.Nodes |> Seq.tryFind (fun c -> rangeContainsPos c.Position pos) with
                            | Some child -> deepestPath (node :: path) child
                            | None -> List.rev (node :: path)
                        let nodePath = deepestPath [] entity.entity
                        let enclosingKey = (nodePath |> List.last).Key
                        if String.IsNullOrWhiteSpace enclosingKey || enclosingKey = "root" then None
                        else
                            let isScriptedDefPath (lp: string) =
                                lp.StartsWith("common/scripted_effects", StringComparison.OrdinalIgnoreCase)
                                || lp.StartsWith("common/scripted_triggers", StringComparison.OrdinalIgnoreCase)
                                || lp.StartsWith("common\\scripted_effects", StringComparison.OrdinalIgnoreCase)
                                || lp.StartsWith("common\\scripted_triggers", StringComparison.OrdinalIgnoreCase)
                            let isTopLevelScriptedDefinition =
                                isScriptedDefPath entity.logicalpath
                                && (match nodePath with
                                    | [ _root; _definition ] -> true
                                    | _ -> false)
                            // 找名为 enclosingKey 的那个定义声明的参数。每个定义文件的「名->参数」表按
                            // 其 Lazy 身份缓存，所以在调用方文件里打字时不会重复折叠 AST（tryPick 命中即停）。
                            let lookupKey = enclosingKey.ToLowerInvariant()
                            let scriptParams =
                                if isTopLevelScriptedDefinition then
                                    []
                                else
                                    resourceManager.Api.AllEntities()
                                    |> Seq.filter (fun struct (e, _) -> isScriptedDefPath e.logicalpath)
                                    |> Seq.tryPick (fun struct (e, l) ->
                                        match Map.tryFind lookupKey (entityScriptedParamMap e (box l)) with
                                        | Some ps when not (List.isEmpty ps) -> Some ps
                                        | _ -> None)
                                    |> Option.defaultValue []
                            if List.isEmpty scriptParams then None
                            else
                                let col = pos.Column
                                let textBefore = if col <= line.Length then line.Substring(0, col) else line
                                // 词首：剥掉光标处正在输入的标识符。
                                let wordStart =
                                    let mutable s = textBefore.Length
                                    while s > 0 && (System.Char.IsLetterOrDigit(textBefore.[s - 1]) || textBefore.[s - 1] = '_') do
                                        s <- s - 1
                                    s
                                // 值位置（紧跟 `key =`）交还常规补全（值可能是 scope/event_target 等）。
                                let isValuePos = textBefore.Substring(0, wordStart).TrimEnd().EndsWith("=")
                                if isValuePos then None
                                else
                                    let currentWord = textBefore.Substring(wordStart)
                                    let filtered =
                                        if currentWord.Length > 0 then
                                            scriptParams |> List.filter (fun p -> p.StartsWith(currentWord, StringComparison.OrdinalIgnoreCase))
                                        else scriptParams
                                    filtered
                                    |> List.mapi (fun i p ->
                                        CompletionResponse.Detailed(p, Some(sprintf "Parameter: %s" p), Some(i + 1), CompletionCategory.Variable))
                                    |> Some

        // 先尝试 @[ expression ] 内部的 scripted_variable 补全
        let exprResult = tryExpressionCompletion()
        match exprResult with
        | Some items ->
            log (sprintf "Expression scripted_variable completion returning %d items" items.Length)
            items
        | None ->

        // 再尝试 inline_script 补全
        let inlineResult = tryInlineScriptCompletion()
        match inlineResult with
        | Some items ->
            log (sprintf "Inline script completion returning %d items" items.Length)
            items
        | None ->
            // 再尝试 script_value 参数补全
            let svResult = tryScriptValueCompletion()
            match svResult with
            | Some items ->
                log (sprintf "ScriptValue completion returning %d items" items.Length)
                items
            | None ->
                // 再尝试 scripted_effect / scripted_trigger 调用块的按定义参数补全
                match tryScriptedEffectParamCompletion() with
                | Some items ->
                    log (sprintf "Scripted effect/trigger param completion returning %d items" items.Length)
                    items
                | None ->

                // 如果是 inline_script 文件，需要找到调用者的上下文
                if isInlineScriptFile then
                    log (sprintf "completion: processing inline_script file, looking for caller context")
                    
                    // 从路径中提取inline_script名称
                    let inlineScriptNameOpt =
                        let pathLower = filepath.ToLowerInvariant()
                        let inlineIdx =
                            let idx1 = pathLower.IndexOf("common/inline_scripts/")
                            let idx2 = pathLower.IndexOf("common\\inline_scripts\\")
                            if idx1 >= 0 then idx1 + "common/inline_scripts/".Length
                            elif idx2 >= 0 then idx2 + "common\\inline_scripts\\".Length
                            else -1
                        
                        if inlineIdx >= 0 && inlineIdx < filepath.Length then
                            let scriptPath = filepath.Substring(inlineIdx).Replace(".txt", "")
                            Some scriptPath
                        else
                            None
                    
                    match inlineScriptNameOpt, processResourceCached () with
                    | Some scriptName, Some inlineEntity ->
                        // 提取脚本的文件名部分(最后一部分)用于搜索
                        let scriptFileName = 
                            scriptName.Split([| '/'; '\\' |]) 
                            |> Array.last
                        
                        log (sprintf "completion: scriptName='%s', scriptFileName='%s'" scriptName scriptFileName)
                        
                        // 检查文件内容是否包含对指定 inline_script 的调用引用
                        // 支持三种匹配模式：
                        //   1. 精确匹配：完整路径或文件名出现在文件中
                        //   2. 参数化路径匹配：将 script 行中的 $PARAM$ 替换为正则通配符后匹配
                        //      例如 script = components/kuat_template_tech_overwrite_$kuat_tech_overwrite$
                        //      匹配 → components/kuat_template_tech_overwrite_yes
                        let fileContainsInlineRef allowPathDefaults (targetScriptName: string) (targetFileName: string) (fileContent: string) =
                            let normTarget = targetScriptName.Replace('\\', '/')
                            // 1. 精确匹配
                            if fileContent.Contains(normTarget, StringComparison.OrdinalIgnoreCase) ||
                               fileContent.Contains(normTarget.Replace('/', '\\'), StringComparison.OrdinalIgnoreCase) then
                                true
                            elif fileContent.Contains(targetFileName, StringComparison.OrdinalIgnoreCase) then
                                true
                            else
                                // 2. 参数化路径匹配：提取所有 script = xxx 行，将 $..$ 替换为正则通配符后匹配
                                let scriptLinePattern = System.Text.RegularExpressions.Regex(@"script\s*=\s*([^\s}]+)")
                                let paramPattern = inlinePathParameterPattern allowPathDefaults
                                let matches = scriptLinePattern.Matches(fileContent)
                                matches
                                |> Seq.cast<System.Text.RegularExpressions.Match>
                                |> Seq.exists (fun m ->
                                    let callPath = m.Groups.[1].Value.Trim()
                                    if callPath.Contains("$") && canMatchParameterizedInlinePath allowPathDefaults callPath then
                                        // 将 $PARAM$ 替换为 .+ 正则通配符
                                        let regexStr = paramPattern.Replace(callPath, ".+").Replace('\\', '/')
                                        try
                                            let regex = System.Text.RegularExpressions.Regex(
                                                "^" + System.Text.RegularExpressions.Regex.Escape(regexStr).Replace(@"\.\+", ".+") + "$",
                                                System.Text.RegularExpressions.RegexOptions.IgnoreCase)
                                            regex.IsMatch(normTarget)
                                        with _ -> false
                                    else false)
                        
                        // 判断一个实体是否在 inline_scripts 目录
                        let isInlineScriptEntity (e: Entity) =
                            e.logicalpath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
                            e.logicalpath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase)
                        
                        // 从实体路径中提取 inline_script 相对名称
                        let extractInlineScriptName (logicalpath: string) =
                            let pathLower = logicalpath.ToLowerInvariant()
                            let inlineIdx =
                                let idx1 = pathLower.IndexOf("common/inline_scripts/")
                                let idx2 = pathLower.IndexOf("common\\inline_scripts\\")
                                if idx1 >= 0 then idx1 + "common/inline_scripts/".Length
                                elif idx2 >= 0 then idx2 + "common\\inline_scripts\\".Length
                                else -1
                            if inlineIdx >= 0 && inlineIdx < logicalpath.Length then
                                Some (logicalpath.Substring(inlineIdx).Replace(".txt", ""))
                            else None
                        
                        let allEntities = resourceManager.Api.AllEntities()
                        
                        // 在指定的实体集合中搜索调用者
                        let findCallerIn (entities: struct (Entity * 'a) seq) (targetName: string) (targetFileName: string) =
                            entities
                            |> Seq.tryPick (fun struct (e, _) ->
                                try
                                    let fileContent = System.IO.File.ReadAllText(e.filepath)
                                    let allowPathDefaults = not (isInlineScriptEntity e)
                                    if fileContainsInlineRef allowPathDefaults targetName targetFileName fileContent then Some e else None
                                with _ -> None)
                        
                        // 递归查找根调用者（非 inline_script 的调用者）
                        // 当直接调用者是另一个 inline_script 文件时，继续向上追溯
                        let rec findRootCaller (targetName: string) (targetFileName: string) (visited: Set<string>) =
                            if visited.Count > 20 then
                                log "completion: exceeded max recursion depth for caller search"
                                None
                            else
                                let newVisited = visited.Add(targetName.ToLowerInvariant())
                                // 优先在 component_templates 目录中搜索非 inline_script 调用者
                                let nonInlineCallerOpt =
                                    allEntities
                                    |> Seq.filter (fun struct (e, _) -> not (isInlineScriptEntity e))
                                    |> Seq.filter (fun struct (e, _) ->
                                        e.logicalpath.Contains("common/component_templates", StringComparison.OrdinalIgnoreCase) ||
                                        e.logicalpath.Contains("common\\component_templates", StringComparison.OrdinalIgnoreCase))
                                    |> findCallerIn <| targetName <| targetFileName
                                    |> function
                                       | Some e -> Some e
                                       | None ->
                                           // 扩展搜索所有非 inline_script 文件
                                           allEntities
                                           |> Seq.filter (fun struct (e, _) -> not (isInlineScriptEntity e))
                                           |> findCallerIn <| targetName <| targetFileName
                                
                                match nonInlineCallerOpt with
                                | Some e -> Some e
                                | None ->
                                    // 在 inline_script 文件中搜索直接调用者（排除自身和已访问的）
                                    let inlineCallerOpt =
                                        allEntities
                                        |> Seq.filter (fun struct (e, _) ->
                                            isInlineScriptEntity e &&
                                            not (newVisited.Contains(
                                                (extractInlineScriptName e.logicalpath |> Option.defaultValue "").ToLowerInvariant())))
                                        |> findCallerIn <| targetName <| targetFileName
                                    
                                    match inlineCallerOpt with
                                    | Some inlineCaller ->
                                        log (sprintf "completion: found inline_script caller '%s', searching upward..." inlineCaller.filepath)
                                        // 直接调用者是 inline_script，递归向上查找根调用者
                                        match extractInlineScriptName inlineCaller.logicalpath with
                                        | Some callerScriptName ->
                                            let callerFileName = callerScriptName.Split([| '/'; '\\' |]) |> Array.last
                                            match findRootCaller callerScriptName callerFileName newVisited with
                                            | Some rootCaller -> Some rootCaller
                                            | None ->
                                                // 找不到根调用者，使用 inline_script 调用者作为备选
                                                log "completion: no root caller found, using inline_script caller as fallback"
                                                Some inlineCaller
                                        | None -> Some inlineCaller
                                    | None -> None
                        
                        let callerEntityOpt = findRootCaller scriptName scriptFileName Set.empty
                        
                        match callerEntityOpt with
                        | Some callerEntity ->
                            log (sprintf "completion: found caller '%s'" callerEntity.filepath)
                            // 收集全局变量
                            let globalVars =
                                try
                                    resourceManager.Api.AllEntities()
                                    |> Seq.choose (fun struct (e, _) ->
                                        if e.filepath.Contains("common/scripted_variables") ||
                                           e.filepath.Contains("common\\scripted_variables") ||
                                           e.logicalpath.Contains("common/scripted_variables") ||
                                           e.logicalpath.Contains("common\\scripted_variables") then
                                            Some e.entity
                                        else
                                            None)
                                    |> Seq.collect CWTools.Validation.Stellaris.STLValidation.getDefinedVariables
                                    |> Seq.filter (fun varName -> not (varName.StartsWith("@[")) && not (varName.StartsWith(@"@\["))) // 过滤掉表达式
                                    |> Seq.distinct
                                    |> Seq.toList
                                with _ -> []

                            let scriptLinePattern = System.Text.RegularExpressions.Regex(@"script\s*=\s*([^\s}]+)")

                            let findScriptLine allowPathDefaults (fileContent: string) (targetScriptFileName: string) (targetScriptName: string) =
                                let lines = fileContent.Split('\n')
                                let normName = targetScriptName.Replace('\\', '/')
                                let mutable found = -1
                                let paramPattern = inlinePathParameterPattern allowPathDefaults

                                for i = 0 to lines.Length - 1 do
                                    if found = -1 then
                                        let line = lines.[i]

                                        if line.Contains(targetScriptFileName, StringComparison.OrdinalIgnoreCase) then
                                            found <- i
                                        else
                                            let m = scriptLinePattern.Match(line)

                                            if m.Success && m.Groups.[1].Value.Contains("$") then
                                                let callPath = m.Groups.[1].Value.Trim()
                                                if canMatchParameterizedInlinePath allowPathDefaults callPath then
                                                    let regexStr = paramPattern.Replace(callPath, ".+").Replace('\\', '/')

                                                    try
                                                        let regex =
                                                            System.Text.RegularExpressions.Regex(
                                                                "^" + System.Text.RegularExpressions.Regex.Escape(regexStr).Replace(@"\.\+", ".+") + "$",
                                                                System.Text.RegularExpressions.RegexOptions.IgnoreCase
                                                            )

                                                        if regex.IsMatch(normName) then
                                                            found <- i
                                                    with _ ->
                                                        ()

                                found

                            let findDirectInlineCallerReferencingTarget () =
                                allEntities
                                |> Seq.tryPick (fun struct (e, _) ->
                                    if isInlineScriptEntity e then
                                        try
                                            let content = System.IO.File.ReadAllText(e.filepath)

                                            if fileContainsInlineRef false scriptName scriptFileName content then
                                                Some e
                                            else
                                                None
                                        with _ ->
                                            None
                                    else
                                        None)

                            // 使用专用的 CompleteInlineScript 方法
                            // 该方法使用 inline_script 实体的 AST 确定当前光标深度，
                            // 同时使用调用者的 logicalpath 匹配类型规则，
                            // 从而正确处理根层和子层的补全

                            match infoService with
                            | Some info ->
                                // Compute caller scope context using rawEntity (which preserves the
                                // original inline_script leaf, unlike entity which has it expanded).
                                let callerScopeCtxOpt =
                                    try
                                        let callerFileContent = System.IO.File.ReadAllText(callerEntity.filepath)
                                        let callerLines = callerFileContent.Split('\n')
                                        let inlineScriptLine =
                                            let directLine = findScriptLine true callerFileContent scriptFileName scriptName

                                            if directLine >= 0 then
                                                directLine
                                            else
                                                findDirectInlineCallerReferencingTarget ()
                                                |> Option.bind (fun directCaller -> extractInlineScriptName directCaller.logicalpath)
                                                |> Option.map (fun intermediateScriptName ->
                                                    let intermediateFileName =
                                                        intermediateScriptName.Split([| '/'; '\\' |]) |> Array.last

                                                    findScriptLine true callerFileContent intermediateFileName intermediateScriptName)
                                                |> Option.defaultValue -1

                                        if inlineScriptLine >= 0 then
                                            // Use rawEntity for GetInfo — the raw AST still has the
                                            // inline_script leaf, so the position matches correctly
                                            // and foldWithPos can accumulate scope from parent blocks.
                                            let rawCallerEntity = { callerEntity with entity = callerEntity.rawEntity }
                                            let lineText = callerLines.[inlineScriptLine].TrimEnd('\r')
                                            let indentCol = lineText.Length - lineText.TrimStart().Length
                                            let callerPos = mkPos (inlineScriptLine + 1) indentCol
                                            info.GetInfo(callerPos, rawCallerEntity) |> Option.map fst
                                        else
                                            None
                                    with _ -> None
                                match completionService with
                                | Some completion ->
                                    // Compute caller's structural rule path.
                                    // For direct inline_scripts: search root caller file for the script reference
                                    // and compute getRulePath on rawEntity.
                                    // For NESTED inline_scripts (target called from another inline_script which
                                    // is called from root): the root caller doesn't contain the target reference.
                                    // In this case, find the DIRECT caller (intermediate inline_script) and chain:
                                    //   rootPath(to intermediate) + intermediatePath(to target)
                                    let callerRulePath =
                                        try
                                            let callerFileContent = System.IO.File.ReadAllText(callerEntity.filepath)
                                            let directLine = findScriptLine true callerFileContent scriptFileName scriptName
                                            if directLine >= 0 then
                                                // Direct reference found in root caller
                                                let callerLines = callerFileContent.Split('\n')
                                                let lineText = callerLines.[directLine].TrimEnd('\r')
                                                let indentCol = lineText.Length - lineText.TrimStart().Length
                                                let callerPos = mkPos (directLine + 1) indentCol
                                                completion.GetRulePath(callerPos, callerEntity.rawEntity)
                                            else
                                                // Not found in root caller — this is a NESTED inline_script.
                                                // Find the direct (intermediate) caller that actually references the target.
                                                let directCallerOpt = findDirectInlineCallerReferencingTarget ()
                                                match directCallerOpt with
                                                | Some directCaller ->
                                                    // Chain paths: root→intermediate + intermediate→target
                                                    // 1. Find root's path to intermediate inline_script
                                                    let intermediateScriptName =
                                                        extractInlineScriptName directCaller.logicalpath
                                                        |> Option.defaultValue ""
                                                    let intermediateFileName =
                                                        intermediateScriptName.Split([| '/'; '\\' |]) |> Array.last
                                                    let rootToIntermediatePath =
                                                        let rootLine = findScriptLine true callerFileContent intermediateFileName intermediateScriptName
                                                        if rootLine >= 0 then
                                                            let callerLines = callerFileContent.Split('\n')
                                                            let lineText = callerLines.[rootLine].TrimEnd('\r')
                                                            let indentCol = lineText.Length - lineText.TrimStart().Length
                                                            let callerPos = mkPos (rootLine + 1) indentCol
                                                            completion.GetRulePath(callerPos, callerEntity.rawEntity)
                                                        else []
                                                    // 2. Find intermediate's path to target inline_script
                                                    let intermediateContent = System.IO.File.ReadAllText(directCaller.filepath)
                                                    let targetLine = findScriptLine false intermediateContent scriptFileName scriptName
                                                    let intermediateToTargetPath =
                                                        if targetLine >= 0 then
                                                            let intermediateLines = intermediateContent.Split('\n')
                                                            let lineText = intermediateLines.[targetLine].TrimEnd('\r')
                                                            let indentCol = lineText.Length - lineText.TrimStart().Length
                                                            let targetPos = mkPos (targetLine + 1) indentCol
                                                            completion.GetRulePath(targetPos, directCaller.rawEntity)
                                                        else []
                                                    // Chain: root path + the direct inline caller path.
                                                    // Inline script files do not have a synthetic type root:
                                                    // the first key in intermediateToTargetPath is a real
                                                    // inserted block and must be preserved (for example
                                                    // trait/icon -> icon -> trait/icon_element/...).
                                                    let rootPrefix =
                                                        rootToIntermediatePath
                                                        |> List.filter (fun (key, _, _, _, _) ->
                                                            not (key = "inline_script" || key = "script"))
                                                    rootPrefix @ intermediateToTargetPath
                                                | None -> []
                                        with _ -> []
                                    completion.CompleteInlineScript(pos, inlineEntity, callerEntity, callerScopeCtxOpt, Some globalVars, callerRulePath)
                                | None -> []
                            | None ->
                                match completionService with
                                | Some completion ->
                                    completion.CompleteInlineScript(pos, inlineEntity, callerEntity, None, Some globalVars, [])
                                | None -> []
                        | None ->
                            log "completion: no caller found, providing basic parameter completion"
                            // 如果找不到调用者,提供参数名补全
                            try
                                let fileContent = System.IO.File.ReadAllText(filepath)
                                let regex = System.Text.RegularExpressions.Regex(@"\$([A-Za-z_][A-Za-z0-9_]*)\$")
                                let matches = regex.Matches(fileContent)
                                let allParams = [ for m in matches -> m.Groups.[1].Value ] |> List.distinct |> List.toArray
                                log (sprintf "completion: found %d params" allParams.Length)
                                allParams
                                |> Array.map (fun param ->
                                    CompletionResponse.Detailed(param, Some($"Parameter: {param}"), None, CompletionCategory.Variable))
                                |> Array.toList
                            with ex -> []
                    | _ ->
                        log "completion: missing required info for inline_script"
                        []
                else
                    // 辅助函数:从 ResourceManager 已缓存的实体中收集全局 scripted variables
                    // 避免文件 I/O 和重复解析，直接使用已加载的实体数据
                    let getGlobalScriptVars () =
                        try
                            resourceManager.Api.AllEntities()
                            |> Seq.choose (fun struct (e, _) ->
                                if e.filepath.Contains("scripted_variables", StringComparison.OrdinalIgnoreCase) ||
                                   e.logicalpath.Contains("scripted_variables", StringComparison.OrdinalIgnoreCase) then
                                    Some e.entity
                                else None)
                            |> Seq.collect CWTools.Validation.Stellaris.STLValidation.getDefinedVariables
                            |> Seq.filter (fun v -> not (v.StartsWith("@[")) && not (v.StartsWith(@"@\[")))
                            |> Seq.distinct
                            |> Seq.toList
                        with _ -> []
                    
                    let globalVars = getGlobalScriptVars ()
                    
                    let completeWithEntity (completion: CompletionService) (infoOpt: InfoService option) (e: Entity) =
                        match infoOpt with
                        | Some info ->
                            log (sprintf "completion %s %s" (fileManager.ConvertPathToLogicalPath filepath) filepath)

                            match info.GetInfo(pos, e) with
                            | Some(ctx, _) -> completion.Complete(pos, e, Some ctx, Some globalVars)
                            | None -> completion.Complete(pos, e, None, Some globalVars)
                        | None -> completion.Complete(pos, e, None, Some globalVars)

                    let completeWithRepairFallback (completion: CompletionService) (infoOpt: InfoService option) =
                        let originalItems =
                            processResourceCached ()
                            |> Option.map (completeWithEntity completion infoOpt)
                            |> Option.defaultValue []

                        if not (List.isEmpty originalItems) then
                            originalItems
                        else
                            processRepairedResourceCached ()
                            |> Option.map (completeWithEntity completion infoOpt)
                            |> Option.defaultValue []

                    // 使用常规补全逻辑
                    match
                        Path.GetExtension filepath, completionService, infoService
                    with
                    | ".yml", Some completion, _ -> completion.LocalisationComplete(pos, filetext) |> List.ofArray
                    | _, Some completion, Some info -> completeWithRepairFallback completion (Some info)
                    | _, Some completion, None -> completeWithRepairFallback completion None
                    | _, _, _ -> []

    let completion
        (fileManager: FileManager)
        (completionService: CompletionService option)
        (infoService: InfoService option)
        (resourceManager: ResourceManager<_>)
        (pos: pos)
        (filepath: string)
        (filetext: string)
        =
        if PdxShaderFeatures.isShaderFile filepath then
            PdxShaderFeatures.completion resourceManager pos filepath filetext
        else
            scriptCompletion fileManager completionService infoService resourceManager pos filepath filetext


    let getInfoAtPos
        (fileManager: FileManager)
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        (localisationManager: LocalisationManager<_>)
        (lookup: Lookup)
        (lang: Lang)
        (pos: pos)
        (filepath: string)
        (filetext: string)
        =
        if PdxShaderFeatures.isShaderFile filepath then
            PdxShaderFeatures.goToDefinition resourceManager.Api pos filepath filetext
        else
            let tryFindTypeDefinition typeName typeValue =
                lookup.typeDefInfo
                |> Map.tryFind typeName
                |> Option.defaultValue [||]
                |> Array.tryPick (fun tdi -> if tdi.id = typeValue then Some tdi.range else None)

            let isEventTypeName (typeName: string) =
                typeName.Equals("event", StringComparison.OrdinalIgnoreCase)
                || typeName.StartsWith("event.", StringComparison.OrdinalIgnoreCase)

            let tryFindAnyEventTypeDefinition typeValue =
                lookup.typeDefInfo
                |> Map.toSeq
                |> Seq.filter (fun (typeName, _) -> isEventTypeName typeName)
                |> Seq.tryPick (fun (_, infos) ->
                    infos |> Array.tryPick (fun tdi -> if tdi.id = typeValue then Some tdi.range else None))

            let primaryResult =
                match processResourceCachedInfo resourceManager fileManager filepath filetext, infoService with
                | Some e, Some info ->
                    logDiag (sprintf "getInfo %s %s" (fileManager.ConvertPathToLogicalPath filepath) filepath)

                    match info.GetInfo(pos, e) with
                    | Some(_, (_, Some(LocRef(tv)), _)) ->
                        match
                            localisationManager.LocalisationEntries()
                            |> Seq.tryFind (fun (l, _) -> l = lang)
                        with
                        | Some(_, entries) ->
                            match entries |> Array.tryFind (fun struct (k, _) -> k = tv) with
                            | Some(_, entry) -> Some entry.position
                            | _ -> None
                        | None -> None
                    | Some(_, (_, Some(TypeRef(t, tv)), _)) ->
                        match tryFindTypeDefinition t tv with
                        | Some _ as range -> range
                        | None when isEventTypeName t -> tryFindAnyEventTypeDefinition tv
                        | None -> None
                    | Some(_, (_, Some(EnumRef(enumName, enumValue)), _)) ->
                        let enumValues = lookup.enumDefs[enumName] |> snd
                        enumValues |> Array.tryPick (fun (ev, r) -> if ev == enumValue then r else None)
                    | Some(_, (_, Some(FileRef f), _)) ->
                        let fNorm = f.Replace("\\", "/")
                        resourceManager.Api.AllEntities()
                        |> Seq.map structFst
                        |> Seq.tryFind (fun x ->
                            let logicalpath = x.logicalpath.Replace("\\", "/")

                            logicalpath.Equals(fNorm, StringComparison.OrdinalIgnoreCase)
                            || (not (fNorm.EndsWith(".txt", StringComparison.OrdinalIgnoreCase))
                                && logicalpath.Equals(fNorm + ".txt", StringComparison.OrdinalIgnoreCase)))
                        |> Option.map (fun x -> mkRange x.filepath pos0 pos0)
                    | _ -> None
                | _, _ -> None

            // Fallback 1: inline_script navigation
            // When the entity has inline_script nodes expanded, GetInfo can't resolve them.
            // Check if the current line contains an inline_script reference and navigate to the target file.
            let inlineScriptFallback () =
                try
                    let split = filetext.Split('\n')
                    let lineIdx = pos.Line - 1
                    if lineIdx < 0 || lineIdx >= split.Length then None
                    else
                        let line = split.[lineIdx]
                        // Match: inline_script = { script = path/to/script ... }
                        // Use \bscript (word boundary) to avoid matching the "script" inside "inline_script"
                        let scriptPattern = System.Text.RegularExpressions.Regex(@"\bscript\s*=\s*([^\s}|]+)")
                        let inlinePattern = System.Text.RegularExpressions.Regex(@"inline_script\s*=")
                        if inlinePattern.IsMatch(line) then
                            let m = scriptPattern.Match(line)
                            if m.Success then
                                let scriptPath = m.Groups.[1].Value.Trim()
                                // Skip parameterized paths (contain $) - they can't be resolved statically
                                if scriptPath.Contains("$") then None
                                else
                                    // Normalize path separators
                                    let normalizedPath = scriptPath.Replace('\\', '/')
                                    // Search all entities for the inline_script file
                                    resourceManager.Api.AllEntities()
                                    |> Seq.map structFst
                                    |> Seq.tryFind (fun e ->
                                        let lp = e.logicalpath.Replace('\\', '/')
                                        (lp.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase)) &&
                                        (lp.EndsWith(normalizedPath + ".txt", StringComparison.OrdinalIgnoreCase) ||
                                         lp.EndsWith(normalizedPath, StringComparison.OrdinalIgnoreCase)))
                                    |> Option.map (fun e -> mkRange e.filepath pos0 pos0)
                            else None
                        else None
                with _ -> None

            // Fallback 2: For inline_script files, extract word at cursor and search type registry
            let wordLookupFallback () =
                let isInlineScript =
                    filepath.Contains("inline_scripts", StringComparison.OrdinalIgnoreCase)
                if not isInlineScript then None
                else
                    try
                        let split = filetext.Split('\n')
                        let lineIdx = pos.Line - 1
                        if lineIdx < 0 || lineIdx >= split.Length then None
                        else
                            let line = split.[lineIdx]
                            let col = pos.Column
                            // Extract word at cursor position (include '/' for inline_script paths)
                            let wordChars c = System.Char.IsLetterOrDigit(c) || c = '_' || c = ':' || c = '.' || c = '/'
                            let mutable startIdx = col
                            while startIdx > 0 && wordChars line.[startIdx - 1] do startIdx <- startIdx - 1
                            let mutable endIdx = col
                            while endIdx < line.Length && wordChars line.[endIdx] do endIdx <- endIdx + 1
                            if startIdx >= endIdx then None
                            else
                                let word = line.Substring(startIdx, endIdx - startIdx)
                                // Search all type definitions for a matching identifier
                                lookup.typeDefInfo
                                |> Map.toSeq
                                |> Seq.tryPick (fun (_, infos) ->
                                    infos |> Array.tryPick (fun tdi ->
                                        if tdi.id = word then Some tdi.range else None))
                    with _ -> None

            let scriptValueFallback () =
                try
                    let split = filetext.Split('\n')
                    let lineIdx = pos.Line - 1
                    if lineIdx < 0 || lineIdx >= split.Length then None
                    else
                        let line = split.[lineIdx].TrimEnd('\r')
                        if line.TrimStart().StartsWith("#") then None
                        else
                            let col = Math.Max(0, Math.Min(pos.Column, line.Length))
                            let isTokenBoundary c =
                                Char.IsWhiteSpace c
                                || c = '='
                                || c = '{'
                                || c = '('
                                || c = '['
                                || c = '<'
                                || c = '>'
                                || c = ','
                                || c = '"'
                                || c = '\''

                            let scriptValueDefinitions =
                                lookup.typeDefInfo
                                |> Map.tryFind "script_value"
                                |> Option.defaultValue [||]

                            if scriptValueDefinitions.Length = 0 then None
                            else
                                let pattern =
                                    System.Text.RegularExpressions.Regex(
                                        @"value:([-A-Za-z0-9_.@/]+)",
                                        System.Text.RegularExpressions.RegexOptions.IgnoreCase
                                    )

                                pattern.Matches(line)
                                |> Seq.cast<System.Text.RegularExpressions.Match>
                                |> Seq.tryPick (fun m ->
                                    let startIdx = m.Index
                                    let endIdx = m.Index + m.Length
                                    let startsAtTokenBoundary = startIdx = 0 || isTokenBoundary line.[startIdx - 1]

                                    if startsAtTokenBoundary && col >= startIdx && col <= endIdx then
                                        let scriptValueName = m.Groups.[1].Value
                                        scriptValueDefinitions
                                        |> Array.tryFind (fun tdi ->
                                            String.Equals(tdi.id, scriptValueName, StringComparison.OrdinalIgnoreCase))
                                        |> Option.map (fun tdi -> tdi.range)
                                    else
                                        None)
                with _ -> None

            match primaryResult with
            | Some _ -> primaryResult
            | None ->
                match inlineScriptFallback () with
                | Some _ as r -> r
                | None ->
                    match scriptValueFallback () with
                    | Some _ as r -> r
                    | None -> wordLookupFallback ()

    let findAllRefsByType
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        (typename: string)
        (typeValue: string)
        =
        let typename = typename.Split('.').[0]
        let typeValue = trimReferenceValue typeValue

        let refsFromTypes =
            getOrBuildTypeReferenceIndex resourceManager infoService
            |> Map.tryFind (typename, typeValue)
            |> Option.defaultValue []

        if refsFromTypes.Length > 0 then
            refsFromTypes
        else
            let rec searchNode (node: Node) =
                [ yield!
                      node.Leaves
                      |> Seq.choose (fun l ->
                          if isSameText l.Key typeValue || isSameText (trimReferenceValue l.ValueText) typeValue then
                              Some l.Position
                          else
                              None)
                  yield!
                      node.LeafValues
                      |> Seq.choose (fun lv ->
                          if isSameText (trimReferenceValue lv.ValueText) typeValue then
                              Some lv.Position
                          else
                              None)
                  yield!
                      node.Nodes
                      |> Seq.choose (fun n -> if isSameText n.Key typeValue then Some n.Position else None)
                  yield! node.Nodes |> Seq.collect searchNode ]

            resourceManager.Api.ValidatableEntities()
            |> List.collect (fun struct (e, _) -> searchNode e.entity)

    let findAllRefsFromPos
        (fileManager: FileManager)
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        (pos: pos)
        (filepath: string)
        (filetext: string)
        =
        let resource = makeEntityResourceInput fileManager filepath filetext

        match resourceManager.ManualProcessResource resource, infoService with
        | Some e, Some info ->
            match info.GetInfo(pos, e) with
            | Some(_, (_, Some(TypeRef(t: string, tv)), _)) ->
                findAllRefsByType resourceManager infoService t tv |> Some
            | _ -> None
        | _, _ -> None



    let scopesAtPos
        (fileManager: FileManager)
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        (anyScope: Scope)
        (pos: pos)
        (filepath: string)
        (filetext: string)
        =
        match processResourceCachedInfo resourceManager fileManager filepath filetext, infoService with
        | Some e, Some info ->
            // match info.GetInfo(pos, e) with
            match info.GetInfo(pos, e) with
            | Some(ctx, _) when
                ctx
                <> { Root = anyScope
                     From = []
                     FromDepth = 0
                     Scopes = [] }
                ->
                Some ctx
            | _ -> None
        | _ -> None


    let symbolInformationAtPos
        (fileManager: FileManager)
        (resourceManager: ResourceManager<_>)
        (infoService: InfoService option)
        (lookup: Lookup)
        (pos: pos)
        (filepath: string)
        (filetext: string)
        : SymbolInformation option =
        // Simple recursive descent evaluator for @[ expr ] expressions
        // Supports: +, -, *, /, unary minus, parentheses, decimal literals, @varName
        let evalExpr (expr: string) (varValues: Map<string, decimal>) : decimal option =
            let mutable pos2 = 0
            let s = expr.Trim()
            let len = s.Length

            let skipWs () =
                while pos2 < len && s.[pos2] = ' ' do pos2 <- pos2 + 1

            let rec parseExpr () =
                skipWs()
                parseAddSub()

            and parseAddSub () =
                let mutable left = parseMulDiv()
                skipWs()
                while pos2 < len && (s.[pos2] = '+' || s.[pos2] = '-') do
                    let op = s.[pos2]
                    pos2 <- pos2 + 1
                    let right = parseMulDiv()
                    left <-
                        match left, right with
                        | Some l, Some r -> Some (if op = '+' then l + r else l - r)
                        | _ -> None
                    skipWs()
                left

            and parseMulDiv () =
                let mutable left = parseUnary()
                skipWs()
                while pos2 < len && (s.[pos2] = '*' || s.[pos2] = '/') do
                    let op = s.[pos2]
                    pos2 <- pos2 + 1
                    let right = parseUnary()
                    left <-
                        match left, right with
                        | Some l, Some r ->
                            if op = '/' && r = 0m then None
                            else Some (if op = '*' then l * r else l / r)
                        | _ -> None
                    skipWs()
                left

            and parseUnary () =
                skipWs()
                if pos2 < len && s.[pos2] = '-' then
                    pos2 <- pos2 + 1
                    parsePrimary() |> Option.map (fun v -> -v)
                else
                    parsePrimary()

            and parsePrimary () =
                skipWs()
                if pos2 >= len then None
                elif s.[pos2] = '(' then
                    pos2 <- pos2 + 1
                    let v = parseExpr()
                    skipWs()
                    if pos2 < len && s.[pos2] = ')' then pos2 <- pos2 + 1
                    v
                elif System.Char.IsLetter(s.[pos2]) || s.[pos2] = '_' then
                    // variable reference without @: varName (in @[ expr ], variables don't have @ prefix)
                    let start = pos2
                    while pos2 < len && (System.Char.IsLetterOrDigit(s.[pos2]) || s.[pos2] = '_' || s.[pos2] = '$') do
                        pos2 <- pos2 + 1
                    let varName = "@" + s.Substring(start, pos2 - start)  // Add @ when looking up
                    varValues |> Map.tryFind varName
                else
                    // number
                    let start = pos2
                    while pos2 < len && (System.Char.IsDigit(s.[pos2]) || s.[pos2] = '.') do
                        pos2 <- pos2 + 1
                    if pos2 > start then
                        match System.Decimal.TryParse(s.Substring(start, pos2 - start), System.Globalization.NumberStyles.Any, System.Globalization.CultureInfo.InvariantCulture) with
                        | true, v -> Some v
                        | _ -> None
                    else
                        pos2 <- pos2 + 1; None

            parseExpr()

        // Collect all scripted variable values from the resource manager
        let getVarValues () : Map<string, decimal> =
            try
                resourceManager.Api.AllEntities()
                |> Seq.filter (fun struct (e, _) ->
                    e.filepath.Contains("common/scripted_variables") ||
                    e.filepath.Contains("common\\scripted_variables") ||
                    e.logicalpath.Contains("common/scripted_variables") ||
                    e.logicalpath.Contains("common\\scripted_variables"))
                |> Seq.collect (fun struct (e, _) ->
                    e.entity.Leaves
                    |> Seq.choose (fun leaf ->
                        if leaf.Key.StartsWith("@") && not (leaf.Key.StartsWith("@[")) && not (leaf.Key.StartsWith(@"@\[")) then
                            match System.Decimal.TryParse(leaf.Value.ToString(), System.Globalization.NumberStyles.Any, System.Globalization.CultureInfo.InvariantCulture) with
                            | true, v -> Some (leaf.Key, v)
                            | _ -> None
                        else None))
                |> Map.ofSeq
            with _ -> Map.empty

        // Format decimal: remove trailing zeros
        let fmtDecimal (d: decimal) =
            let s = d.ToString("G29", System.Globalization.CultureInfo.InvariantCulture)
            s

        // Check if cursor is on an inline_script call - show evaluated expressions from the script
        let split = filetext.Split('\n')
        let lineIdx = pos.Line - 1

        let tryGetInlineScriptInfo () =
            if lineIdx >= 0 && lineIdx < split.Length then
                let line = split.[lineIdx]
                // Only show evaluated expressions when hovering on the "script = ..." key in the block
                if not (System.Text.RegularExpressions.Regex(@"\bscript\s*=").IsMatch(line)) then
                    None
                else
                    // Search upward for inline_script block
                let mutable foundScript = None
                let mutable i = lineIdx
                let mutable braceDepth = 0

                // Count braces on current line up to cursor
                let line = split.[lineIdx]
                let col = pos.Column
                let curLineUpToCursor = if col <= line.Length then line.Substring(0, col) else line
                braceDepth <- curLineUpToCursor.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                braceDepth <- braceDepth - (curLineUpToCursor.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length)

                i <- lineIdx
                while i >= 0 && foundScript.IsNone do
                    let l = split.[i]
                    let opens = l.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                    let closes = l.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                    braceDepth <- braceDepth + closes - opens

                    if braceDepth <= 0 && l.Contains("inline_script") then
                        // Found inline_script block, now collect parameters
                        let mutable paramMap = Map.empty
                        let mutable scriptPath = None

                        // Find the end of this block
                        let rec findBlockEnd lineIdx currentDepth =
                            if lineIdx >= split.Length then lineIdx - 1
                            else
                                let lineText = split.[lineIdx]
                                let opens = lineText.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                                let closes = lineText.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                                let newDepth = currentDepth + opens - closes
                                if newDepth <= 0 then lineIdx
                                else findBlockEnd (lineIdx + 1) newDepth
                        
                        let initialOpens = split.[i].ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                        let endBlockIdx = if initialOpens > 0 then findBlockEnd (i + 1) initialOpens else i

                        let kvPattern = System.Text.RegularExpressions.Regex(@"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*("".*?""|[^\s{}#]+)")

                        for j = i to endBlockIdx do
                            let m = kvPattern.Match(split.[j])
                            if m.Success then
                                let key = m.Groups.[1].Value
                                let mutable value = m.Groups.[2].Value
                                // Strip quotes so math evaluation can work
                                if value.StartsWith("\"") && value.EndsWith("\"") && value.Length >= 2 then
                                    value <- value.Substring(1, value.Length - 2)

                                if key = "script" then
                                    scriptPath <- Some value
                                else
                                    paramMap <- paramMap |> Map.add key value

                        match scriptPath with
                        | Some path ->
                            // Try to find and read the inline_script file
                            try
                                let scriptFilePath =
                                    // Try common/inline_scripts/{path}, then {path}.txt
                                    let currentDir = System.IO.Path.GetDirectoryName(filepath)
                                    let rec findModRoot dir =
                                        if System.String.IsNullOrEmpty(dir) then None
                                        else
                                            let dirName = System.IO.Path.GetFileName(dir)
                                            if dirName = "common" || dirName = "events" then
                                                Some(System.IO.Path.GetDirectoryName(dir))
                                            else
                                                findModRoot (System.IO.Path.GetDirectoryName(dir))

                                    match findModRoot currentDir with
                                    | Some modRoot ->
                                        let scriptFile =
                                            System.IO.Path.Combine(modRoot, "common", "inline_scripts", path)

                                        let scriptFileTxt = scriptFile + ".txt"

                                        if System.IO.File.Exists(scriptFile) then
                                            Some scriptFile
                                        elif System.IO.File.Exists(scriptFileTxt) then
                                            Some scriptFileTxt
                                        else
                                            None
                                    | None -> None

                                match scriptFilePath with
                                | Some scriptFile ->
                                    let scriptContent = System.IO.File.ReadAllText(scriptFile)
                                    let scriptLines = scriptContent.Split('\n')
                                    // Extract all @[...] expressions from the script
                                    let exprPattern = System.Text.RegularExpressions.Regex(@"@\[([^\]]+)\]")
                                    let exprMatches = exprPattern.Matches(scriptContent)

                                    if exprMatches.Count > 0 then
                                        let varValues = getVarValues()
                                        let paramPattern = System.Text.RegularExpressions.Regex(@"\$([A-Za-z0-9_]+)(?:\|[^$]*)?\$")
                                        let varRefPattern = System.Text.RegularExpressions.Regex(@"@([A-Za-z_][A-Za-z0-9_]*)")

                                        let results =
                                            exprMatches
                                            |> Seq.cast<System.Text.RegularExpressions.Match>
                                            |> Seq.choose (fun m ->
                                                let exprContent = m.Groups.[1].Value.Trim()

                                                // Find the line context (e.g., "min = @[...]" → "min")
                                                let lineContext =
                                                    let exprPos = m.Index
                                                    let mutable charCount = 0
                                                    let mutable lineNum = -1
                                                    for li = 0 to scriptLines.Length - 1 do
                                                        let lineLen = scriptLines.[li].Length + 1 // +1 for \n
                                                        if charCount <= exprPos && exprPos < charCount + lineLen then
                                                            lineNum <- li
                                                        charCount <- charCount + lineLen
                                                    if lineNum >= 0 && lineNum < scriptLines.Length then
                                                        let l = scriptLines.[lineNum].Trim()
                                                        // Extract the key before = @[
                                                        let eqIdx = l.IndexOf("=")
                                                        if eqIdx > 0 then l.Substring(0, eqIdx).Trim()
                                                        else ""
                                                    else ""

                                                // Collect @variable values used in this expression
                                                let varRefs =
                                                    varRefPattern.Matches(exprContent)
                                                    |> Seq.cast<System.Text.RegularExpressions.Match>
                                                    |> Seq.choose (fun vm ->
                                                        let varName = "@" + vm.Groups.[1].Value
                                                        match varValues |> Map.tryFind varName with
                                                        | Some v -> Some (varName, fmtDecimal v)
                                                        | None -> None)
                                                    |> Seq.distinctBy fst
                                                    |> Seq.toList

                                                // Collect $PARAM$ values used in this expression
                                                let paramRefs =
                                                    paramPattern.Matches(exprContent)
                                                    |> Seq.cast<System.Text.RegularExpressions.Match>
                                                    |> Seq.choose (fun pm ->
                                                        let paramName = pm.Groups.[1].Value
                                                        match paramMap |> Map.tryFind paramName with
                                                        | Some value -> Some (sprintf "$%s$" paramName, value)
                                                        | None -> None)
                                                    |> Seq.distinctBy fst
                                                    |> Seq.toList

                                                // Substitute parameters
                                                let instantiated =
                                                    paramPattern.Matches(exprContent)
                                                    |> Seq.cast<System.Text.RegularExpressions.Match>
                                                    |> Seq.fold (fun (expr: string) pm ->
                                                        let paramName = pm.Groups.[1].Value
                                                        match paramMap |> Map.tryFind paramName with
                                                        | Some value -> expr.Replace(pm.Value, value)
                                                        | None -> expr) exprContent

                                                // Substitute @variables for display
                                                let fullySubstituted =
                                                    varRefPattern.Matches(instantiated)
                                                    |> Seq.cast<System.Text.RegularExpressions.Match>
                                                    |> Seq.fold (fun (expr: string) vm ->
                                                        let varName = "@" + vm.Groups.[1].Value
                                                        match varValues |> Map.tryFind varName with
                                                        | Some v -> expr.Replace(vm.Value, fmtDecimal v)
                                                        | None -> expr) instantiated

                                                match evalExpr instantiated varValues with
                                                | Some v ->
                                                    Some (exprContent, lineContext, varRefs, paramRefs, fullySubstituted, fmtDecimal v)
                                                | None -> None)
                                            |> Seq.toArray

                                        if results.Length > 0 then
                                            let resultStrs =
                                                results |> Array.map (fun (expr, ctx, vars, parms, subst, res) ->
                                                    if ctx <> "" then sprintf "**%s** = **%s**" ctx res
                                                    else sprintf "`@[ %s ]` = **%s**" expr res)

                                            let allResults = String.concat "\n\n---\n\n" resultStrs
                                            foundScript <- Some (path, allResults)
                                | None -> ()
                            with _ -> ()
                        | None -> ()
                    i <- i - 1

                foundScript
            else
                None

        match tryGetInlineScriptInfo() with
        | Some (scriptPath, results) ->
            Some
                { name = sprintf "inline_script: %s" scriptPath
                  typename = "inline_script"
                  localisation = []
                  ruleDescription = Some (sprintf "Evaluated expressions:\n\n%s" results)
                  ruleRequiredScopes = [] }
        | None ->

        // Check if cursor is on a @[ expression ] - provide expression info with evaluation
        if lineIdx >= 0 && lineIdx < split.Length then
            let line = split.[lineIdx]
            let col = pos.Column
            let textBefore = if col <= line.Length then line.Substring(0, col) else line
            let lastOpen = max (textBefore.LastIndexOf("@[")) (textBefore.LastIndexOf(@"@\["))
            let lastClose = textBefore.LastIndexOf("]")
            if lastOpen >= 0 && lastOpen > lastClose then
                let closeIdx = line.IndexOf("]", lastOpen)
                if closeIdx > lastOpen then
                    // Determine prefix length (@[ = 2, @\[ = 3)
                    let prefixLen = if line.Substring(lastOpen).StartsWith(@"@\[") then 3 else 2
                    let exprContent = line.Substring(lastOpen + prefixLen, closeIdx - lastOpen - prefixLen).Trim()

                    // Check if expression contains $PARAM$ placeholders
                    let paramPattern = System.Text.RegularExpressions.Regex(@"\$([A-Za-z0-9_]+)(?:\|[^$]*)?\$")
                    let paramMatches = paramPattern.Matches(exprContent)

                    let varValues = getVarValues()

                    // Try to extract parameter values from the surrounding inline_script call context
                    // e.g. inline_script = { script = path SIZE = 1 TIER = 2 }
                    let tryGetInlineScriptParams () : Map<string, string> =
                        // Search upward from current line for inline_script block
                        // Collect all key = value pairs within the same brace level
                        let mutable paramMap = Map.empty
                        let mutable braceDepth = 0
                        let mutable foundInlineScript = false
                        let mutable i = lineIdx
                        // First, count closing braces on current line up to cursor
                        let curLineUpToCursor = if col <= line.Length then line.Substring(0, col) else line
                        braceDepth <- curLineUpToCursor.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                        braceDepth <- braceDepth - (curLineUpToCursor.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length)
                        i <- lineIdx - 1
                        while i >= 0 && not foundInlineScript do
                            let l = split.[i]
                            let opens = l.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                            let closes = l.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                            braceDepth <- braceDepth + closes - opens
                            if braceDepth <= 0 then
                                // We're at the opening brace level - check if this is inline_script
                                if l.Contains("inline_script") then
                                    foundInlineScript <- true
                                else
                                    // Not inline_script, stop searching
                                    i <- -1
                            i <- i - 1
                        if foundInlineScript then
                            // Now collect all key = value pairs between the inline_script braces
                            // Re-scan from the inline_script line downward to current line
                            let startLine = i + 2  // i was decremented one extra time
                            let kvPattern = System.Text.RegularExpressions.Regex(@"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([^\s{}#]+)")
                            for j = startLine to lineIdx do
                                let l = split.[j].Trim()
                                // Skip script = xxx line
                                if not (l.StartsWith("script")) then
                                    let m = kvPattern.Match(split.[j])
                                    if m.Success then
                                        paramMap <- paramMap |> Map.add m.Groups.[1].Value m.Groups.[2].Value
                        paramMap

                    let varRefPattern = System.Text.RegularExpressions.Regex(@"@([A-Za-z_][A-Za-z0-9_]*)")

                    // Extract the field context from the current line (e.g., "min = @[...]" → "min")
                    let lineContext =
                        let trimmed = line.Trim()
                        let eqIdx = trimmed.IndexOf("=")
                        if eqIdx > 0 then trimmed.Substring(0, eqIdx).Trim() else ""

                    // Collect @variable values used in this expression
                    let varRefs =
                        varRefPattern.Matches(exprContent)
                        |> Seq.cast<System.Text.RegularExpressions.Match>
                        |> Seq.choose (fun vm ->
                            let varName = "@" + vm.Groups.[1].Value
                            match varValues |> Map.tryFind varName with
                            | Some v -> Some (varName, fmtDecimal v)
                            | None -> None)
                        |> Seq.distinctBy fst
                        |> Seq.toList

                    // Determine the result with detailed info
                    let makeDetailedResult (instantiated: string) (callSiteParams: Map<string, string>) =
                        // Collect $PARAM$ values
                        let paramRefs =
                            paramMatches
                            |> Seq.cast<System.Text.RegularExpressions.Match>
                            |> Seq.choose (fun pm ->
                                let paramName = pm.Groups.[1].Value
                                match callSiteParams |> Map.tryFind paramName with
                                | Some value -> Some (sprintf "$%s$" paramName, value)
                                | None -> None)
                            |> Seq.distinctBy fst
                            |> Seq.toList

                        // Substitute @variables for display
                        let fullySubstituted =
                            varRefPattern.Matches(instantiated)
                            |> Seq.cast<System.Text.RegularExpressions.Match>
                            |> Seq.fold (fun (expr: string) vm ->
                                let varName = "@" + vm.Groups.[1].Value
                                match varValues |> Map.tryFind varName with
                                | Some v -> expr.Replace(vm.Value, fmtDecimal v)
                                | None -> expr) instantiated

                        match evalExpr instantiated varValues with
                        | Some v ->
                            let res = fmtDecimal v

                            if lineContext <> "" then sprintf "**%s** = **%s**" lineContext res
                            else sprintf "`@[ %s ]` = **%s**" exprContent res
                        | None ->
                            let unresolved =
                                paramMatches
                                |> Seq.cast<System.Text.RegularExpressions.Match>
                                |> Seq.map (fun m -> m.Groups.[1].Value)
                                |> Seq.distinct |> Seq.toArray
                            if unresolved.Length > 0 then
                                sprintf "`@[ %s ]`\n\n(parameters: %s)" exprContent (String.concat ", " unresolved)
                            else
                                sprintf "`@[ %s ]` (could not evaluate)" exprContent

                    let detailedText =
                        if paramMatches.Count = 0 then
                            // No parameters - evaluate directly
                            makeDetailedResult exprContent Map.empty
                        else
                            // Has $PARAM$ placeholders - try to get actual values from call site
                            let callSiteParams = tryGetInlineScriptParams()
                            if callSiteParams.Count > 0 then
                                let instantiated =
                                    paramMatches
                                    |> Seq.cast<System.Text.RegularExpressions.Match>
                                    |> Seq.fold (fun (expr: string) m ->
                                        let paramName = m.Groups.[1].Value
                                        match callSiteParams |> Map.tryFind paramName with
                                        | Some value -> expr.Replace(m.Value, value)
                                        | None -> expr) exprContent
                                makeDetailedResult instantiated callSiteParams
                            else
                                // No call site params found - show template info
                                let paramNames =
                                    paramMatches
                                    |> Seq.cast<System.Text.RegularExpressions.Match>
                                    |> Seq.map (fun m -> m.Groups.[1].Value)
                                    |> Seq.distinct |> Seq.toArray
                                let header =
                                    if lineContext <> "" then sprintf "**%s** = `@[ %s ]`" lineContext exprContent
                                    else sprintf "`@[ %s ]`" exprContent
                                let varLines = varRefs |> List.map (fun (name, value) -> sprintf "- `%s` = `%s`" name value)
                                let paramLines = paramNames |> Array.toList |> List.map (fun p -> sprintf "- `$%s$` — *parameter*" p)
                                String.concat "\n" ([header; "\n"] @ varLines @ paramLines)

                    Some
                        { name = exprContent
                          typename = "expression"
                          localisation = []
                          ruleDescription = Some detailedText
                          ruleRequiredScopes = [] }
                else None
            else None
        else None
        |> function
        | Some info -> Some info
        | None ->

        match processResourceCachedInfo resourceManager fileManager filepath filetext, infoService with
        | Some e, Some info ->
            log (sprintf "symbolInfoAtPos %s %s" (fileManager.ConvertPathToLogicalPath filepath) filepath)

            let ruleOptions, typeInfo, nodeAtPos =
                info.GetInfo(pos, e)
                |> Option.map snd
                |> Option.map (fun (rd, ti, child) ->
                    child
                    |> function
                        | Some(NodeC node) -> rd, ti, Some node
                        | _ -> rd, ti, None)
                |> Option.defaultValue (None, None, None)

            let tv, t, locs =
                match typeInfo with
                | Some(TypeRef(t, tv)) ->
                    let splitType = t.Split '.'
                    let typename = splitType.[0]
                    let subtype = if splitType.Length > 1 then splitType.[1] else ""

                    match lookup.typeDefs |> List.tryFind (fun td -> td.name = typename) with
                    | Some td ->
                        let locs =
                            td.localisation
                            @ (td.subtypes
                               |> List.collect (fun st -> if st.name = subtype then st.localisation else []))

                        let typeDefNode = getNodeForTypeDefAndType resourceManager lookup td tv

                        match typeDefNode |> Option.orElse nodeAtPos with
                        | Some node ->
                            tv,
                            tv,
                            locs
                            |> List.map (fun l ->
                                match l.explicitField with
                                | None ->
                                    { key = l.name
                                      value = (l.prefix + tv + l.suffix) }
                                | Some field ->
                                    { key = l.name
                                      value = node.TagText field })
                        | None ->
                            tv,
                            t,
                            locs
                            |> List.choose (fun l ->
                                if l.explicitField.IsNone then
                                    Some
                                        { key = l.name
                                          value = (l.prefix + tv + l.suffix) }
                                else
                                    None)
                    | None -> "", "", []
                | Some(FileRef f) ->
                    // Find the actual file for preview
                    let fNorm = f.Replace("\\", "/")
                    let fileEntity =
                        resourceManager.Api.AllEntities()
                        |> Seq.map structFst
                        |> Seq.tryFind (fun x ->
                            let logicalpath = x.logicalpath.Replace("\\", "/")

                            logicalpath.Equals(fNorm, StringComparison.OrdinalIgnoreCase)
                            || (not (fNorm.EndsWith(".txt", StringComparison.OrdinalIgnoreCase))
                                && logicalpath.Equals(fNorm + ".txt", StringComparison.OrdinalIgnoreCase)))
                    let previewText =
                        match fileEntity with
                        | Some entity ->
                            try
                                let content = System.IO.File.ReadAllText(entity.filepath)
                                let lines = content.Split('\n')
                                let maxLines = min lines.Length 20
                                let preview = lines |> Array.take maxLines |> String.concat "\n"
                                if lines.Length > maxLines then preview + "\n..."
                                else preview
                            with _ -> ""
                        | None -> ""
                    let displayPath = fNorm.Replace("/", " / ")
                    f, "inline_script_file", [{ key = "path"; value = displayPath }; { key = "preview"; value = previewText }]
                | None -> "", "", []
                | _ -> "", "", []

            Some
                { name = tv
                  typename = t
                  localisation = locs
                  ruleDescription = ruleOptions |> Option.bind (fun ro -> ro.description)
                  ruleRequiredScopes =
                    ruleOptions
                    |> Option.map (fun ro -> ro.requiredScopes |> List.map (fun s -> s.ToString()))
                    |> Option.defaultValue [] }
        | _, _ -> None


    let getPreTriggerPossible
        (fileManager: FileManager)
        (resourceManager: ResourceManager<_>)
        (filepath: string)
        (filetext: string)
        =
        let resource = makeEntityResourceInput fileManager filepath filetext

        match resourceManager.ManualProcessResource resource with
        | Some e ->
            if e.logicalpath.StartsWith "events" then
                let findEvents (event: Node) =
                    match event.Key == "planet_event", event.Child "trigger" with
                    | _, None -> None
                    | false, _ -> None
                    | true, Some trigger ->
                        if
                            Array.exists
                                trigger.Has
                                CWTools.Validation.Stellaris.STLValidation.stellarisEventPreTriggers
                        then
                            Some event.Position
                        else
                            None

                e.entity.Children |> List.choose findEvents
            else if e.logicalpath.StartsWith "common/pop_jobs" then
                let findPopJobs (popjob: Node) =
                    match popjob.Child "possible" with
                    | None -> None
                    | Some possible ->
                        if
                            Array.exists
                                possible.Has
                                CWTools.Validation.Stellaris.STLValidation.stellarisPopJobPreTriggers
                        then
                            Some popjob.Position
                        else
                            None

                e.entity.Children |> List.choose findPopJobs
            else
                []
        | None -> []

    let getFastTrigger
        (fileManager: FileManager)
        (resourceManager: ResourceManager<_>)
        (filepath: string)
        (filetext: string)
        =
        let resource = makeEntityResourceInput fileManager filepath filetext

        let extractPreTrigger (node: Node) (key: string) =
            if node.Has key then
                let leaf = node.Leafs key |> Seq.head
                let text = leaf.Key + " = " + leaf.ValueText
                let range = leaf.Position
                Some(range, text)
            else
                None

        let pretriggerBlockForEvent
            (targetblock: string)
            (sourceblock: string)
            (event: Node)
            (pretriggers: string seq)
            =
            let ptTemplate (tabs: string) (pt: string) = sprintf "\t%s\n%s" pt tabs

            let createAllPts (tabs: string) =
                pretriggers |> Seq.map (ptTemplate tabs) |> String.concat ""

            if event.Has targetblock then
                let endPos = event.Childs targetblock |> Seq.head |> (fun c -> c.Position.End)
                let tabCount = endPos.Column - 1
                let tabString = String.replicate tabCount "\t"
                let ptText = createAllPts tabString
                let ptInsert = mkPos endPos.Line (endPos.Column - 1), ptText
                ptInsert
            else
                let startTriggerPos =
                    event.Childs sourceblock |> Seq.head |> (fun c -> c.Position.Start)

                let tabCount = startTriggerPos.Column
                let tabString = String.replicate tabCount "\t"
                let ptText = createAllPts tabString
                let ptBlock = sprintf "%s = {\n%s%s}\n%s" targetblock tabString ptText tabString
                let ptInsert = startTriggerPos, ptBlock
                ptInsert

        match resourceManager.ManualProcessResource resource with
        | Some e ->
            if e.logicalpath.StartsWith "events" then
                let eventToChanges (event: Node) =
                    match event.Key == "planet_event", event.Child "trigger" with
                    | true, Some trigger ->
                        let triggers =
                            CWTools.Validation.Stellaris.STLValidation.stellarisEventPreTriggers
                            |> Seq.choose (extractPreTrigger trigger)
                            |> List.ofSeq

                        match triggers with
                        | [] -> None
                        | triggers ->
                            let insertPos, insertText =
                                pretriggerBlockForEvent "pre_triggers" "trigger" event (triggers |> Seq.map snd)

                            let deletes = triggers |> Seq.map fst
                            Some(deletes, insertPos, insertText)
                    | _, _ -> None

                Some(e.entity.Children |> List.choose eventToChanges)
            else if e.logicalpath.StartsWith "common/pop_jobs" then
                let eventToChanges (event: Node) =
                    match event.Child "possible" with
                    | Some trigger ->
                        let triggers =
                            CWTools.Validation.Stellaris.STLValidation.stellarisPopJobPreTriggers
                            |> Seq.choose (extractPreTrigger trigger)
                            |> List.ofSeq

                        match triggers with
                        | [] -> None
                        | triggers ->
                            let insertPos, insertText =
                                pretriggerBlockForEvent
                                    "possible_pre_triggers"
                                    "possible"
                                    event
                                    (triggers |> Seq.map snd)

                            let deletes = triggers |> Seq.map fst
                            Some(deletes, insertPos, insertText)
                    | _ -> None

                Some(e.entity.Children |> List.choose eventToChanges)
            else
                None
        | _ -> None

    // type CachedRuleMetadata = {
    //     typeDefs : Map<string,list<TypeDefInfo>>
    //     enumDefs : Map<string,string * list<string>>
    //     varDefs : Map<string,list<string * range>>
    //     loc : (Lang * Set<string>) list
    //     files : Set<string>
    // }
    let getEmbeddedMetadata (lookup: Lookup) (localisation: LocalisationManager<_>) (resources: ResourceManager<_>) =
        { typeDefs = lookup.typeDefInfo
          enumDefs = lookup.enumDefs |> Map.map (fun _ (s, v) -> s, v |> Array.map fst)
          varDefs = lookup.varDefInfo
          loc = localisation.LocalisationKeys()
          files = resources.Api.GetFileNames() |> Set.ofSeq
          scriptedLoc = lookup.scriptedLoc }


    let graphEventDataForFiles
        (referenceManager: References<_>)
        (resourceManager: ResourceManager<_>)
        (lookup: Lookup)
        (files: string list)
        (sourceType: string)
        (depth: int)
        : GraphDataItem list =
        let sourceTypes =
            lookup.typeDefs
            |> List.tryPick (fun td ->
                if td.name = sourceType then
                    Some(sourceType :: td.graphRelatedTypes)
                else
                    None)
            |> Option.defaultValue [ sourceType ]

        let entitiesInSelectedFiles =
            resourceManager.Api.AllEntities()
            |> Seq.filter (fun struct (e, _) -> files |> List.contains e.filepath)
            |> Seq.toList

        let locSet = referenceManager.Localisation |> Map.ofList

        let findLoc key =
            locSet |> Map.tryFind key |> Option.map (fun l -> l.desc)

        let getSourceTypesTD (x: Map<string, TypeDefInfo array>) =
            Map.toList x
            |> List.filter (fun (k, _) -> sourceTypes |> List.contains k)
            |> List.collect (fun (k, vs) ->
                vs
                |> Array.map (fun tdi -> k, tdi.id, tdi.range, tdi.explicitLocalisation, tdi.subtypes)
                |> List.ofSeq)

        let getSourceTypes (x: Map<string, ReferenceDetails list>) =
            Map.toList x
            |> List.filter (fun (k, _) -> sourceTypes |> List.contains k)
            |> List.collect (fun (k, vs) ->
                vs
                |> List.map (fun rd -> k, rd.name, rd.position, rd.isOutgoing, rd.referenceLabel, []))

        let getNonExplicitLoc (id: string) (typeName: string) =
            lookup.typeDefs
            |> List.tryPick (fun td -> if td.name = typeName then Some td.localisation else None)
            |> Option.bind (fun ls -> ls |> List.tryFind (fun l -> l.explicitField.IsNone && l.primary))
            |> Option.bind (fun l -> l.prefix + id + l.suffix |> findLoc)

        let getDisplayNameFromID (id: string) (el: (string * string * bool) list) (entityType: string) =
            el
            |> List.tryFind (fun (_, _, primary) -> primary)
            |> Option.bind (fun (_, key, _) -> findLoc key)
            |> Option.orElseWith (fun _ -> getNonExplicitLoc id entityType)
            |> Option.orElseWith (fun _ -> findLoc id)

        let getAbbrevInfo (typeName: string) (subtypes: string list) =
            lookup.typeDefs
            |> List.tryPick (fun td -> if td.name = typeName then Some td.subtypes else None)
            |> Option.defaultValue []
            |> List.filter (fun st -> st.abbreviation.IsSome || st.displayName.IsSome)
            |> List.tryFind (fun st -> subtypes |> List.contains st.name)


        match lookup.typeDefInfo |> getSourceTypesTD with
        | [] -> []
        | t ->
            let typesDefinedInFiles =
                t |> List.filter (fun (_, _, r, el, _) -> files |> List.contains r.FileName)

            let allInternalOrOutgoingRefs =
                entitiesInSelectedFiles
                |> List.collect (fun struct (_, data) ->
                    data.Force().Referencedtypes
                    |> Option.map (
                        getSourceTypes
                        >> List.map (fun (_, v, r, isOutgoing, refLabel, _) -> (v, r, isOutgoing, refLabel))
                    )
                    |> Option.defaultValue [])

            let definedVariables =
                entitiesInSelectedFiles
                |> List.collect (fun struct (_, data) ->
                    data.Force().Definedvariables
                    |> Option.map (
                        Map.toList
                        >> List.collect (fun (k, vs) -> vs |> List.ofSeq |> List.map (fun (v1, v2) -> k, v1, v2))
                    )
                    |> Option.defaultValue [])

            let results =
                typesDefinedInFiles
                |> List.map (fun (entityType, event, r, el, sts) ->
                    entityType,
                    event,
                    r,
                    (allInternalOrOutgoingRefs
                     |> List.choose (fun (reference, r2, isOutgoing, refLabel) ->
                         if rangeContainsRange r r2 then
                             Some(reference.GetString(), isOutgoing, refLabel)
                         else
                             None)
                     |> List.distinct),
                    (definedVariables
                     |> List.choose (fun (varname, defVar, r2) ->
                         if rangeContainsRange r r2 then
                             Some(varname, defVar)
                         else
                             None)
                     |> List.distinct),
                    el,
                    sts)

            let primaries =
                results
                |> List.map (fun (entityType, event, r, refs, defvar, el, sts) ->
                    let subtypeName, abbrev =
                        getAbbrevInfo entityType sts
                        |> Option.map (fun st -> st.displayName, st.abbreviation)
                        |> Option.defaultValue (None, None)

                    { GraphDataItem.id = event
                      displayName = getDisplayNameFromID event el entityType
                      documentation = None
                      references = refs
                      location = Some r
                      details =
                        Some(
                            defvar
                            |> List.groupBy fst
                            |> List.map (fun (k, vs) -> k, vs |> List.map snd)
                            |> Map.ofList
                        )
                      isPrimary = true
                      entityType = entityType
                      entityTypeDisplayName = subtypeName
                      abbreviation = abbrev })

            let allInternalOrOutgoingRefNames =
                allInternalOrOutgoingRefs
                |> List.map (fun (r, _, _, _) -> r.GetString())
                |> List.distinct

            let allTypeNamesInFiles = typesDefinedInFiles |> List.map (fun (k, n, r, _, _) -> n)

            let allOutgoingRefs =
                t
                |> List.filter (fun (k, name, _, _, _) ->
                    allInternalOrOutgoingRefNames |> List.contains name
                    && (allTypeNamesInFiles |> List.contains name |> not))
                |> List.distinctBy (fun (_, name, _, _, _) -> name)

            let secondaryNames = allOutgoingRefs |> List.map (fun (k, n, r, _, _) -> n)
            // let allOtherFiles = t |> List.filter (fun (_, id, range, _, _) -> files |> List.contains range.FileName |> not)
            //                              |> List.map (fun (_, _, range, _, _) -> range.FileName)
            // let get
            let getNewIncomingRefs (excludedFiles: string list) (targetTypeNames: string list) =
                let allOtherFiles =
                    t
                    |> List.filter (fun (_, id, range, _, _) -> excludedFiles |> List.contains range.FileName |> not)
                    |> List.map (fun (_, _, range, _, _) -> range.FileName)

                let newIncomingRefs =
                    resourceManager.Api.AllEntities()
                    |> Seq.filter (fun struct (e, _) -> allOtherFiles |> List.contains e.filepath)
                    |> Seq.collect (fun struct (_, data) ->
                        data.Force().Referencedtypes
                        |> Option.map (
                            getSourceTypes
                            >> List.map (fun (_, v, r, isOutgoing, refLabel, _) ->
                                (v.GetString(), r, isOutgoing, refLabel))
                        )
                        |> Option.defaultValue [])
                    |> Seq.filter (fun (v, r, isOutgoing, refLabel) -> targetTypeNames |> List.contains v)
                    |> Seq.toList

                newIncomingRefs

            let getTypesFromRefs (previouslyScannedTypes: string list) refs =
                t
                |> List.filter (fun (_, name, r, el, _) ->
                    (previouslyScannedTypes |> List.contains name |> not)
                    && (secondaryNames |> List.contains name |> not))
                |> List.filter (fun (_, _, r, _, _) ->
                    refs
                    |> List.exists (fun (_, r2, isOutgoing, refLabel) -> rangeContainsRange r r2))

            let searchBackwards typesToSearchBackFrom allPreviousTypes =
                let typesToSearchBackFromNames =
                    typesToSearchBackFrom |> List.map (fun (k, n, r, _, _) -> n)

                let allIncoming = getNewIncomingRefs files typesToSearchBackFromNames
                let allNewTypes = getTypesFromRefs allPreviousTypes allIncoming
                allIncoming, allNewTypes, typesToSearchBackFromNames

            let folder (allRefs, backTypes, backSearched, allBackTypes) =
                let nextBackRefs, nextBackTypes, nextNowSearched =
                    searchBackwards backTypes backSearched

                allRefs @ nextBackRefs, nextBackTypes, nextNowSearched @ backSearched, nextBackTypes @ allBackTypes

            let allIncomingRefs, _, _, allIncomingTypes =
                repeatN folder depth ([], typesDefinedInFiles, allTypeNamesInFiles, [])

            let secondaries =
                allOutgoingRefs @ allIncomingTypes
                |> List.map (fun (entityType, name, range, el, sts) ->
                    let subtypeName, abbrev =
                        getAbbrevInfo entityType sts
                        |> Option.map (fun st -> st.displayName, st.abbreviation)
                        |> Option.defaultValue (None, None)

                    { GraphDataItem.id = name
                      displayName = getDisplayNameFromID name el entityType
                      documentation = None
                      references =
                        (allIncomingRefs
                         |> List.choose (fun (reference, r2, isOutgoing, refLabel) ->
                             if rangeContainsRange range r2 then
                                 Some(reference, isOutgoing, refLabel)
                             else
                                 None)
                         |> List.distinct)
                      location = Some range
                      details = None
                      isPrimary = false
                      entityType = entityType
                      entityTypeDisplayName = subtypeName |> Option.orElse (Some entityType)
                      abbreviation = abbrev })

            primaries @ secondaries
