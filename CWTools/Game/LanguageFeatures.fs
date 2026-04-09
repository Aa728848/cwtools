namespace CWTools.Games

open System
open CWTools.Utilities.Position
open System.IO
open Files
open CWTools.Utilities.Utils
open CWTools.Process
open CWTools.Rules
open CWTools.Common
open CWTools.Parser

module LanguageFeatures =

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


    let completion
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

        let resource = makeEntityResourceInput fileManager filepath filetext

        // 检测当前文件是否是 inline_script 文件
        let isInlineScriptFile =
            filepath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
            filepath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase)

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

                    match findInlineScriptContext currentLineIdx 0 0 with
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
                                // Find the closing brace of the inline_script block
                                let rec findBlockEnd lineIdx braceDepth =
                                    if lineIdx >= split.Length then lineIdx - 1
                                    else
                                        let l = split.[lineIdx].Trim()
                                        let openBraces = l.ToCharArray() |> Array.filter (fun c -> c = '{') |> Array.length
                                        let closeBraces = l.ToCharArray() |> Array.filter (fun c -> c = '}') |> Array.length
                                        let newDepth = braceDepth + openBraces - closeBraces
                                        if newDepth <= 0 then lineIdx
                                        else findBlockEnd (lineIdx + 1) newDepth
                                let blockEndLine = findBlockEnd (inlineScriptLineIdx + 1) 1

                                // Now search all lines within [inlineScriptLineIdx .. blockEndLine]
                                let mutable result = None
                                for i in inlineScriptLineIdx .. blockEndLine do
                                    if result.IsNone && i >= 0 && i < split.Length then
                                        let l = split.[i].Trim()
                                        // Skip lines with inline_script keyword
                                        if not (l.Contains("inline_script")) then
                                            let scriptPattern = System.Text.RegularExpressions.Regex(@"^\s*script\s*=\s*([^\s}]+)")
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
                                    if hasParamInPath then
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

                                    // Detect if cursor is in value position (after = sign)
                                    let isAfterEquals =
                                        let lineText = split.[currentLineIdx]
                                        let cursorCol = min col lineText.Length
                                        if cursorCol > 0 then
                                            let textBefore = lineText.Substring(0, cursorCol)
                                            let lastEq = textBefore.LastIndexOf('=')
                                            if lastEq >= 0 then
                                                let afterEq = textBefore.Substring(lastEq + 1).Trim()
                                                not (afterEq.Contains("="))
                                            else false
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
                        let valuePattern = System.Text.RegularExpressions.Regex(@"value\s*:\s*([^|\s]+)\|")
                        let m = valuePattern.Match(line.Substring(0, searchEnd))

                        if m.Success then
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
                                    let allEntities = resourceManager.Api.AllEntities()
                                    let extractParams (e: Entity) =
                                        let getDollarText (s: string) acc =
                                            s.Split('$')
                                            |> Array.mapi (fun i s -> i, s)
                                            |> Array.fold (fun acc (i, s) ->
                                                if i % 2 = 1 then
                                                    match s.Split('|') with
                                                    | [| name; _ |] -> name :: acc
                                                    | _ -> s :: acc
                                                else acc) acc
                                        let fNode = (fun (x: Node) acc ->
                                            let nodeRes = getDollarText x.Key acc
                                            x.Leaves |> Seq.fold (fun a leaf ->
                                                getDollarText leaf.Key (getDollarText (leaf.Value.ToRawString()) a)) nodeRes)
                                        e.entity |> (ProcessCore.foldNode7 fNode) |> List.ofSeq

                                    let allParams =
                                        allEntities
                                        |> Seq.filter (fun struct (e, _) ->
                                            e.logicalpath.Contains("common/script_values", StringComparison.OrdinalIgnoreCase) ||
                                            e.logicalpath.Contains("common\\script_values", StringComparison.OrdinalIgnoreCase))
                                        |> Seq.collect (fun struct (e, _) -> extractParams e)
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
                        else
                            // 情况2：刚输入 | 但文档中可能还没有 - value:xxx 后面紧跟 |
                            // 检查光标前是否有 value:xxx 模式（没有 |）
                            let valueNoPipePattern = System.Text.RegularExpressions.Regex(@"value\s*:\s*([^|\s]+)$")
                            let textBeforeCursor =
                                if searchEnd <= line.Length then line.Substring(0, searchEnd)
                                else line
                            let m2 = valueNoPipePattern.Match(textBeforeCursor)

                            if m2.Success then
                                let scriptValueName = m2.Groups.[1].Value
                                let endOfMatch = m2.Index + m2.Length
                                // 确认光标就在 value:xxx 末尾或后面紧跟 |
                                if col >= endOfMatch - 1 && col <= endOfMatch + 1 then
                                    // 直接从所有实体中提取 script_value 参数
                                    let allEntities = resourceManager.Api.AllEntities()
                                    let extractParams (e: Entity) =
                                        let getDollarText (s: string) acc =
                                            s.Split('$')
                                            |> Array.mapi (fun i s -> i, s)
                                            |> Array.fold (fun acc (i, s) ->
                                                if i % 2 = 1 then
                                                    match s.Split('|') with
                                                    | [| name; _ |] -> name :: acc
                                                    | _ -> s :: acc
                                                else acc) acc
                                        let fNode = (fun (x: Node) acc ->
                                            let nodeRes = getDollarText x.Key acc
                                            x.Leaves |> Seq.fold (fun a leaf ->
                                                getDollarText leaf.Key (getDollarText (leaf.Value.ToRawString()) a)) nodeRes)
                                        e.entity |> (ProcessCore.foldNode7 fNode) |> List.ofSeq

                                    let allParams =
                                        allEntities
                                        |> Seq.filter (fun struct (e, _) ->
                                            e.logicalpath.Contains("common/script_values", StringComparison.OrdinalIgnoreCase) ||
                                            e.logicalpath.Contains("common\\script_values", StringComparison.OrdinalIgnoreCase))
                                        |> Seq.collect (fun struct (e, _) -> extractParams e)
                                        |> Seq.distinct
                                        |> Seq.toArray

                                    if allParams.Length > 0 then
                                        log (sprintf "ScriptValue completion (no pipe) params: %A" allParams)
                                        let completionItems =
                                            allParams
                                            |> Array.map (fun p ->
                                                CompletionResponse.Simple(p, None, CompletionCategory.Value))
                                            |> Array.toList
                                        log (sprintf "ScriptValue completion (no pipe) items count: %d" completionItems.Length)
                                        Some completionItems
                                    else
                                        None
                                else
                                    None
                            else
                                None
                    else
                        None
            else
                None

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
                    
                    match inlineScriptNameOpt, resourceManager.ManualProcessResource resource with
                    | Some scriptName, Some inlineEntity ->
                        // 提取脚本的文件名部分(最后一部分)用于搜索
                        let scriptFileName = 
                            scriptName.Split([| '/'; '\\' |]) 
                            |> Array.last
                        
                        // 遍历所有非inline_scripts的实体,找到调用者
                        let allEntities = resourceManager.Api.AllEntities()
                        
                        // 优先查找component_templates目录下的文件
                        let callerEntityOpt =
                            allEntities
                            |> Seq.filter (fun struct (e, _) ->
                                // 排除inline_scripts目录
                                let callerPath = e.logicalpath
                                not (callerPath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
                                     callerPath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase)))
                            |> Seq.filter (fun struct (e, _) ->
                                // 只查找component_templates目录
                                e.logicalpath.Contains("common/component_templates", StringComparison.OrdinalIgnoreCase) ||
                                e.logicalpath.Contains("common\\component_templates", StringComparison.OrdinalIgnoreCase))
                            |> Seq.tryPick (fun struct (e, _) ->
                                try
                                    let fileContent = System.IO.File.ReadAllText(e.filepath)
                                    // 检查是否包含脚本文件名
                                    if fileContent.Contains(scriptFileName, StringComparison.OrdinalIgnoreCase) then
                                        Some e
                                    else
                                        None
                                with _ -> None)
                            |> function
                               | Some e -> Some e
                               | None ->
                                   // 如果component_templates中没找到,扩展搜索所有文件
                                   allEntities
                                   |> Seq.filter (fun struct (e, _) ->
                                       let callerPath = e.logicalpath
                                       not (callerPath.Contains("common/inline_scripts", StringComparison.OrdinalIgnoreCase) ||
                                            callerPath.Contains("common\\inline_scripts", StringComparison.OrdinalIgnoreCase)))
                                   |> Seq.tryPick (fun struct (e, _) ->
                                       try
                                           let fileContent = System.IO.File.ReadAllText(e.filepath)
                                           if fileContent.Contains(scriptFileName, StringComparison.OrdinalIgnoreCase) then
                                               Some e
                                           else
                                               None
                                       with _ -> None)
                        
                        match callerEntityOpt with
                        | Some callerEntity ->
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

                            // 关键修复：使用专用的 CompleteInlineScript 方法
                            // 该方法使用 inline_script 实体的 AST 确定当前光标深度，
                            // 同时使用调用者的 logicalpath 匹配类型规则，
                            // 从而正确处理根层和子层的补全

                            match infoService with
                            | Some info ->
                                // 使用调用者实体获取 scope 上下文（从调用者的 inline_script 引用位置）
                                let callerScopeCtxOpt =
                                    try
                                        let callerFileContent = System.IO.File.ReadAllText(callerEntity.filepath)
                                        let callerLines = callerFileContent.Split([| '\n'; '\r' |], StringSplitOptions.RemoveEmptyEntries)
                                        let mutable inlineScriptLine = -1
                                        for i = 0 to callerLines.Length - 1 do
                                            if inlineScriptLine = -1 && callerLines.[i].Contains(scriptFileName, StringComparison.OrdinalIgnoreCase) then
                                                inlineScriptLine <- i
                                        if inlineScriptLine >= 0 then
                                            let callerPos = mkPos (inlineScriptLine + 1) (callerLines.[inlineScriptLine].Length)
                                            info.GetInfo(callerPos, callerEntity) |> Option.map fst
                                        else
                                            None
                                    with _ -> None
                                match completionService with
                                | Some completion ->
                                    // 使用专用的 CompleteInlineScript 方法：
                                    // - 使用 inline_script 实体的 AST 确定当前光标深度
                                    // - 使用调用者的 logicalpath 匹配类型规则
                                    // - 正确处理根层和子层的补全
                                    completion.CompleteInlineScript(pos, inlineEntity, callerEntity, callerScopeCtxOpt, Some globalVars)
                                | None -> []
                            | None ->
                                match completionService with
                                | Some completion ->
                                    completion.CompleteInlineScript(pos, inlineEntity, callerEntity, None, Some globalVars)
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
                    // 辅助函数:动态收集全局 scripted variables
                    // 直接从文件系统读取 scripted_variables 文件
                    let getGlobalScriptVars () =
                        try
                            // 从当前文件路径推断出 mod/游戏根目录
                            let currentDir = System.IO.Path.GetDirectoryName(filepath)
                            
                            // 向上查找 common 目录的父目录(即 mod 根目录)
                            let rec findModRoot dir =
                                if System.String.IsNullOrEmpty(dir) then None
                                else
                                    let dirName = System.IO.Path.GetFileName(dir)
                                    if dirName = "common" || dirName = "events" || dirName = "interface" then
                                        Some(System.IO.Path.GetDirectoryName(dir))
                                    else
                                        findModRoot (System.IO.Path.GetDirectoryName(dir))
                            
                            match findModRoot currentDir with
                            | None -> []
                            | Some modRoot ->
                                // 搜索 mod 根目录下的 common/scripted_variables
                                let svPath = System.IO.Path.Combine(modRoot, "common", "scripted_variables")
                                
                                if not (System.IO.Directory.Exists(svPath)) then
                                    // 可能在游戏本体或其他 mod 中
                                    let gameRoot = System.IO.Path.GetDirectoryName(modRoot)
                                    if System.String.IsNullOrEmpty(gameRoot) then
                                        []
                                    else
                                        let modDir = System.IO.Path.Combine(gameRoot, "mod")
                                        if not (System.IO.Directory.Exists(modDir)) then
                                            []
                                        else
                                            let mutable allVars = []
                                            let modFolders = System.IO.Directory.GetDirectories(modDir)
                                            
                                            for modFolder in modFolders do
                                                let modSVPath = System.IO.Path.Combine(modFolder, "common", "scripted_variables")
                                                if System.IO.Directory.Exists(modSVPath) then
                                                    let files = System.IO.Directory.GetFiles(modSVPath, "*.txt", System.IO.SearchOption.AllDirectories)
                                                    
                                                    for file in files do
                                                        try
                                                            // 使用 FileManager 创建 EntityResourceInput
                                                            let input = makeEntityResourceInput fileManager file (System.IO.File.ReadAllText(file))
                                                            match resourceManager.ManualProcessResource input with
                                                            | Some entity ->
                                                                let vars = CWTools.Validation.Stellaris.STLValidation.getDefinedVariables entity.entity
                                                                            |> List.filter (fun v -> not (v.StartsWith("@[")) && not (v.StartsWith(@"@\[")))
                                                                allVars <- vars @ allVars
                                                            | _ -> ()
                                                        with _ -> ()
                                            
                                            allVars |> List.distinct
                                else
                                    let files = System.IO.Directory.GetFiles(svPath, "*.txt", System.IO.SearchOption.AllDirectories)
                                    
                                    files
                                    |> Array.map (fun file ->
                                        try
                                            let input = makeEntityResourceInput fileManager file (System.IO.File.ReadAllText(file))
                                            match resourceManager.ManualProcessResource input with
                                            | Some entity ->
                                                CWTools.Validation.Stellaris.STLValidation.getDefinedVariables entity.entity
                                                |> List.filter (fun v -> not (v.StartsWith("@[")) && not (v.StartsWith(@"@\[")))
                                            | _ -> []
                                        with _ -> [])
                                    |> Array.toList
                                    |> List.collect id
                                    |> List.distinct
                        with ex -> 
                            []
                    
                    let globalVars = getGlobalScriptVars ()
                    
                    // 使用常规补全逻辑
                    match
                        Path.GetExtension filepath, resourceManager.ManualProcessResource resource, completionService, infoService
                    with
                    | ".yml", _, Some completion, _ -> completion.LocalisationComplete(pos, filetext) |> List.ofArray
                    | _, Some e, Some completion, Some info ->
                        log (sprintf "completion %s %s" (fileManager.ConvertPathToLogicalPath filepath) filepath)

                        match info.GetInfo(pos, e) with
                        | Some(ctx, _) -> completion.Complete(pos, e, Some ctx, Some globalVars)
                        | None -> completion.Complete(pos, e, None, Some globalVars)
                    | _, Some e, Some completion, None -> completion.Complete(pos, e, None, Some globalVars)
                    | _, _, _, _ -> []


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
        let resource = makeEntityResourceInput fileManager filepath filetext

        let primaryResult =
            match resourceManager.ManualProcessResource resource, infoService with
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
                    lookup.typeDefInfo
                    |> Map.tryFind t
                    |> Option.defaultValue [||]
                    |> Array.tryPick (fun tdi -> if tdi.id = tv then Some tdi.range else None)
                | Some(_, (_, Some(EnumRef(enumName, enumValue)), _)) ->
                    let enumValues = lookup.enumDefs[enumName] |> snd
                    enumValues |> Array.tryPick (fun (ev, r) -> if ev == enumValue then r else None)
                | Some(_, (_, Some(FileRef f), _)) ->
                    let fNorm = f.Replace("\\", "/")
                    resourceManager.Api.AllEntities()
                    |> Seq.map structFst
                    |> Seq.tryFind (fun x -> x.logicalpath.Replace("\\", "/").Equals(fNorm, StringComparison.OrdinalIgnoreCase))
                    |> Option.map (fun x -> mkRange x.filepath pos0 pos0)
                | _ -> None
            | _, _ -> None

        // Fallback for inline_script files: if primary lookup failed,
        // extract the word at cursor and search the type registry directly
        match primaryResult with
        | Some _ -> primaryResult
        | None ->
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
                        // Extract word at cursor position
                        let wordChars c = System.Char.IsLetterOrDigit(c) || c = '_' || c = ':' || c = '.'
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
            log (sprintf "findRefs %s %s" (fileManager.ConvertPathToLogicalPath filepath) filepath)

            match info.GetInfo(pos, e) with
            | Some(_, (_, Some(TypeRef(t: string, tv)), _)) ->
                //log "tv %A %A" t tv
                let t = t.Split('.').[0]

                resourceManager.Api.ValidatableEntities()
                |> List.choose (fun struct (e, l) ->
                    let x = l.Force().Referencedtypes in

                    if x.IsSome then
                        (x.Value.TryFind t)
                    else
                        let contains, value = (info.GetReferencedTypes e).TryGetValue t in
                        if contains then Some(value |> List.ofSeq) else None)
                |> List.collect id
                |> List.choose (fun ref ->
                    if ref.name.GetString() == tv && ref.referenceType = ReferenceType.TypeDef then
                        Some ref.position
                    else
                        None)
                |> Some
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
        let resource = makeEntityResourceInput fileManager filepath filetext

        match resourceManager.ManualProcessResource resource, infoService with
        | Some e, Some info ->
            // match info.GetInfo(pos, e) with
            match info.GetInfo(pos, e) with
            | Some(ctx, _) when
                ctx
                <> { Root = anyScope
                     From = []
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
        let resource = makeEntityResourceInput fileManager filepath filetext

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
                                    // Try common/inline_scripts/{path}.txt
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
                                        let scriptFile = System.IO.Path.Combine(modRoot, "common", "inline_scripts", path + ".txt")
                                        if System.IO.File.Exists(scriptFile) then Some scriptFile else None
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
                                        let paramPattern = System.Text.RegularExpressions.Regex(@"\$([A-Za-z0-9_]+)\$")
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
                    let paramPattern = System.Text.RegularExpressions.Regex(@"\$([A-Za-z0-9_]+)\$")
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

        match resourceManager.ManualProcessResource resource, infoService with
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
                        |> Seq.tryFind (fun x -> x.logicalpath.Replace("\\", "/").Equals(fNorm, StringComparison.OrdinalIgnoreCase))
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
            // let allIncomingRefs = getNewIncomingRefs files allTypeNamesInFiles
            // let typesNotDefinedInFiles = getTypesFromRefs allTypeNamesInFiles allIncomingRefs
            // let typesNotDefinedInFilesNames = typesNotDefinedInFiles |> List.map (fun (k, n, r, _, _) -> n)
            // let allIncomingMinusOneRefs = getNewIncomingRefs files typesNotDefinedInFilesNames
            // let typesNotDefinedInFilesMinusOne = getTypesFromRefs (allTypeNamesInFiles @ typesNotDefinedInFilesNames) allIncomingMinusOneRefs
            // let typesNotDefinedInFilesMinusOneNames = typesNotDefinedInFilesMinusOne |> List.map (fun (k, n, r, _, _) -> n)
            // let allIncomingMinusTwoRefs = getNewIncomingRefs files typesNotDefinedInFilesMinusOneNames
            // let typesNotDefinedInFilesMinusTwo = getTypesFromRefs (allTypeNamesInFiles @ typesNotDefinedInFilesNames @ typesNotDefinedInFilesMinusOneNames) allIncomingMinusTwoRefs
            let searchBackwards typesToSearchBackFrom allPreviousTypes =
                let typesToSearchBackFromNames =
                    typesToSearchBackFrom |> List.map (fun (k, n, r, _, _) -> n)

                let allIncoming = getNewIncomingRefs files typesToSearchBackFromNames
                let allNewTypes = getTypesFromRefs allPreviousTypes allIncoming
                allIncoming, allNewTypes, typesToSearchBackFromNames
            // let directBackRefs, directBackTypes, directNowSearched = searchBackwards typesNotDefinedInFiles allTypeNamesInFiles
            // let minusOneBackRefs, minusOneBackTypes, minusOneNowSearched = searchBackwards directBackTypes (directNowSearched @ allTypeNamesInFiles)
            let folder (allRefs, backTypes, backSearched, allBackTypes) =
                let nextBackRefs, nextBackTypes, nextNowSearched =
                    searchBackwards backTypes backSearched

                allRefs @ nextBackRefs, nextBackTypes, nextNowSearched @ backSearched, nextBackTypes @ allBackTypes

            let allIncomingRefs, _, _, allIncomingTypes =
                repeatN folder depth ([], typesDefinedInFiles, allTypeNamesInFiles, [])
            // let allIncomingRefs = resourceManager.Api.AllEntities() |> List.filter (fun struct(e, _) -> allOtherFiles |> List.contains e.filepath)
            //                         |> List.collect (fun struct(_, data) -> data.Force().Referencedtypes |> Option.map (getSourceTypes >> List.map (fun (_, v, r, isOutgoing, refLabel, _) -> (v, r, isOutgoing, refLabel))) |> Option.defaultValue [])
            //                         |> List.filter (fun (v, r, isOutgoing, refLabel) -> allTypeNamesInFiles |> List.contains v)
            // let typesNotDefinedInFiles = t |> List.filter (fun (_, name, r, el, _) -> (allTypeNamesInFiles |> List.contains name |> not) && (secondaryNames |> List.contains name |> not))
            //                                |> List.filter (fun (_, _, r, _, _) -> allIncomingRefs |> List.exists (fun (_, r2, isOutgoing, refLabel) -> rangeContainsRange r r2))
            // let allRefs = allIncomingRefs @ allIncomingMinusOneRefs @ allIncomingMinusTwoRefs
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
