namespace CWTools.Games

open System
open System.Collections.Generic
open System.IO
open System.Runtime.InteropServices
open System.Security.Cryptography
open System.Text
open PdxShaderSyntax
open PdxShaderPreprocessor
open CWTools.Utilities.Position

/// Document snapshots, origin precedence and per-root compile units for the FX shader DSL.
///
/// A compile unit is a root .shader file plus the transitive closure of its Includes.
/// Only symbols from the current document's compile unit are visible to LSP features;
/// unrelated shader files never contribute symbols. Path comparison is case-insensitive
/// only on Windows; display paths keep their original casing.
module PdxShaderProject =

    /// Small lock-external bounded LRU used by immutable shader snapshots.  A
    /// content hash is part of every key, so moving an entry only affects
    /// eviction order and can never change the value observed by another
    /// document version.
    type private BoundedLruCache<'Key, 'Value when 'Key: equality>(capacity: int) =
        let capacity = max 1 capacity
        let entries = Dictionary<'Key, LinkedListNode<'Key * 'Value>>()
        let recency = LinkedList<'Key * 'Value>()

        member _.TryGet(key: 'Key) =
            match entries.TryGetValue key with
            | true, node ->
                recency.Remove node
                recency.AddFirst node
                Some(snd node.Value)
            | _ -> None

        member _.Set(key: 'Key, value: 'Value) =
            match entries.TryGetValue key with
            | true, node ->
                node.Value <- key, value
                recency.Remove node
                recency.AddFirst node
            | _ ->
                let node = recency.AddFirst((key, value))
                entries[key] <- node

                if entries.Count > capacity then
                    let oldest = recency.Last

                    if not (isNull oldest) then
                        recency.Remove oldest
                        entries.Remove(fst oldest.Value) |> ignore

        member _.Count = entries.Count

        member _.Clear() =
            entries.Clear()
            recency.Clear()

    /// Origin of a shader document. Lower rank wins when several snapshots share a
    /// logical path: current unsaved document > workspace/mod > dependency > vanilla.
    type ShaderOrigin =
        | CurrentDocument
        | Workspace
        | Dependency of loadOrder: int
        | Vanilla

    let originRank =
        function
        | CurrentDocument -> 0
        | Workspace -> 1
        | Dependency _ -> 2
        | Vanilla -> 3

    let private dependencyOrder =
        function
        | Dependency order -> order
        | _ -> 0

    /// Path comparison is case-insensitive only on Windows (project rule).
    let pathComparison =
        if RuntimeInformation.IsOSPlatform OSPlatform.Windows then
            StringComparison.OrdinalIgnoreCase
        else
            StringComparison.Ordinal

    let private caseFold (value: string) =
        if pathComparison = StringComparison.OrdinalIgnoreCase then
            value.ToLowerInvariant()
        else
            value

    /// Full path with normalized separators, case-folded on Windows. Used only as a key;
    /// the original casing is kept in ShaderSnapshot.displayPath.
    let canonicalizePath (path: string) =
        let full = safeGetFullPath path
        full.Replace('\\', '/').TrimEnd('/') |> caseFold

    /// Logical-path key: forward slashes, no leading slash, case-folded on Windows.
    let normalizeLogicalPath (path: string) =
        path.Replace('\\', '/').TrimStart('/') |> caseFold

    let sameFilePath left right =
        String.Equals(canonicalizePath left, canonicalizePath right, StringComparison.Ordinal)

    let isShaderFile (filepath: string) =
        let extension = Path.GetExtension filepath
        extension.Equals(".shader", StringComparison.OrdinalIgnoreCase)
        || extension.Equals(".fxh", StringComparison.OrdinalIgnoreCase)

    /// LSP position from a raw text offset; shared by the shader LSP features.
    let posFromOffset (text: string) offset =
        let targetOffset = max 0 (min text.Length offset)
        let mutable line = 1
        let mutable column = 0
        let mutable i = 0

        while i < targetOffset do
            if text[i] = '\n' then
                line <- line + 1
                column <- 0
            elif text[i] <> '\r' then
                column <- column + 1

            i <- i + 1

        CWTools.Utilities.Position.mkPos line column
    type ShaderLoadOrderRoot =
        { name: string
          path: string
          origin: ShaderOrigin }

    let private loadOrderLock = obj ()
    let mutable private loadOrderRoots: ShaderLoadOrderRoot list = []

    /// Configure explicit project/dependency roots in the order supplied by the
    /// LSP workspace. The first root is the editable workspace; later roots are
    /// dependencies. No directory enumeration is used to invent an order.
    let configureLoadOrderRoots (roots: (string * string) list) =
        let configured =
            roots
            |> List.mapi (fun index (name, path) ->
                { name = name
                  path = canonicalizePath path
                  origin = if index = 0 then Workspace else Dependency(index - 1) })
            |> List.filter (fun root -> not (String.IsNullOrWhiteSpace root.path))
            |> List.distinctBy _.path
        lock loadOrderLock (fun () -> loadOrderRoots <- configured)

    let resetLoadOrderRoots () = lock loadOrderLock (fun () -> loadOrderRoots <- [])

    let configuredLoadOrderRoots () = lock loadOrderLock (fun () -> loadOrderRoots)

    let private pathIsInside (root: string) (candidate: string) =
        candidate = root
        || (candidate.Length > root.Length
            && candidate.StartsWith(root, StringComparison.Ordinal)
            && candidate[root.Length] = '/')

    /// Pure provenance resolver used by the project and fixture tests.
    let originForResourceWithRoots (roots: ShaderLoadOrderRoot list) (scope: string) (filepath: string) =
        if not (isNull scope) && scope.Equals("vanilla", StringComparison.OrdinalIgnoreCase) then Vanilla
        elif not (isNull scope) && scope.Equals("embedded", StringComparison.OrdinalIgnoreCase) then Dependency Int32.MaxValue
        else
            let candidate = canonicalizePath filepath
            roots
            |> List.filter (fun root -> pathIsInside root.path candidate)
            |> List.sortByDescending (fun root -> root.path.Length)
            |> List.tryHead
            |> Option.map _.origin
            |> Option.orElseWith (fun () ->
                roots
                |> List.tryFind (fun root -> root.name.Equals(scope, StringComparison.OrdinalIgnoreCase))
                |> Option.map _.origin)
            |> Option.defaultValue Workspace

    /// Resolve resource provenance from explicit root metadata. Vanilla remains
    /// authoritative by scope; unknown scopes conservatively stay Workspace.
    let originForResource (scope: string) (filepath: string) =
        originForResourceWithRoots (configuredLoadOrderRoots ()) scope filepath

    let private isEscapedQuote (text: string) index =
        let mutable slashCount = 0
        let mutable i = index - 1

        while i >= 0 && text[i] = '\\' do
            slashCount <- slashCount + 1
            i <- i - 1

        slashCount % 2 = 1

    /// Immutable document snapshot. logicalPath keeps its original form for display;
    /// always compare it through normalizeLogicalPath.
    type ShaderSnapshot =
        { canonicalPath: string
          displayPath: string
          logicalPath: string
          origin: ShaderOrigin
          text: string
          contentHash: string }

    type ShaderSemanticSnapshot =
        { syntax: ShaderSyntaxTree
          preprocessor: PreprocessorResult
          hlsl: PdxShaderHlsl.HlslAnalysis }

    let contentHashForText (text: string) =
        let safeText = if isNull text then "" else text
        safeText |> Encoding.UTF8.GetBytes |> SHA256.HashData |> Convert.ToHexString

    /// Stable ordering: origin rank, dependency load order, then canonical path.
    let sortKey (snapshot: ShaderSnapshot) =
        (originRank snapshot.origin, dependencyOrder snapshot.origin, snapshot.canonicalPath)

    let createSnapshot origin filepath logicalpath text =
        let full = safeGetFullPath filepath

        let safeText = if isNull text then "" else text

        { canonicalPath = canonicalizePath filepath
          displayPath = full
          logicalPath =
            if String.IsNullOrWhiteSpace logicalpath then
                filepath
            else
                logicalpath
          origin = origin
          text = safeText
          contentHash = contentHashForText safeText }

    let private semanticCacheCap = 256
    let private semanticCache = BoundedLruCache<string * string, ShaderSemanticSnapshot>(semanticCacheCap)
    let private semanticCacheLock = obj ()

    /// Authoritative syntax/preprocessor/HLSL snapshot consumed by every feature.
    let semanticSnapshot (snapshot: ShaderSnapshot) =
        let key = snapshot.canonicalPath, snapshot.contentHash

        lock semanticCacheLock (fun () ->
            match semanticCache.TryGet key with
            | Some cached -> cached
            | None ->
                let syntax = PdxShaderSyntax.parse snapshot.displayPath snapshot.text
                let preprocessor = PdxShaderPreprocessor.analyze syntax
                let hlsl = PdxShaderHlsl.analyze syntax preprocessor
                let parsed =
                    { syntax = syntax
                      preprocessor = preprocessor
                      hlsl = hlsl }

                semanticCache.Set(key, parsed)
                parsed)

    /// Keep string offsets stable while removing comments, preprocessors and embedded HLSL.
    /// Shared with PdxShaderFeatures so both layers scan identical DSL surfaces.
    let cleanDslText (text: string) =
        let chars = text.ToCharArray()
        let mutable i = 0
        let mutable inString = false

        let blankNonNewline i =
            if chars[i] <> '\r' && chars[i] <> '\n' then chars[i] <- ' '

        let blankUntilLineEnd start =
            let mutable j = start

            while j < chars.Length && chars[j] <> '\r' && chars[j] <> '\n' do
                blankNonNewline j
                j <- j + 1

            j

        while i < chars.Length do
            if not inString && i + 1 < chars.Length && chars[i] = '[' && chars[i + 1] = '[' then
                blankNonNewline i
                blankNonNewline (i + 1)
                i <- i + 2
                let mutable doneHlsl = false

                while i < chars.Length && not doneHlsl do
                    if i + 1 < chars.Length && chars[i] = ']' && chars[i + 1] = ']' then
                        blankNonNewline i
                        blankNonNewline (i + 1)
                        i <- i + 2
                        doneHlsl <- true
                    else
                        blankNonNewline i
                        i <- i + 1
            elif not inString && i + 1 < chars.Length && chars[i] = '/' && chars[i + 1] = '*' then
                blankNonNewline i
                blankNonNewline (i + 1)
                i <- i + 2
                let mutable doneComment = false

                while i < chars.Length && not doneComment do
                    if i + 1 < chars.Length && chars[i] = '*' && chars[i + 1] = '/' then
                        blankNonNewline i
                        blankNonNewline (i + 1)
                        i <- i + 2
                        doneComment <- true
                    else
                        blankNonNewline i
                        i <- i + 1
            elif not inString && i + 1 < chars.Length && chars[i] = '/' && chars[i + 1] = '/' then
                i <- blankUntilLineEnd i
            elif not inString && chars[i] = '#' then
                i <- blankUntilLineEnd i
            else
                if chars[i] = '"' && not (isEscapedQuote text i) then inString <- not inString
                i <- i + 1

        String(chars)

    /// Include target plus its offset/length in the including file's original text.
    type IncludeEntry =
        { target: string
          start: int
          length: int
          condition: PresenceCondition }

    let private unquoteIncludeArgument (argument: string) =
        let trimmed = argument.Trim()

        if trimmed.Length >= 2
           && ((trimmed[0] = '"' && trimmed[trimmed.Length - 1] = '"')
               || (trimmed[0] = '<' && trimmed[trimmed.Length - 1] = '>')) then
            Some(trimmed.Substring(1, trimmed.Length - 2))
        else
            None

    let private extractIncludesRaw (snapshot: ShaderSnapshot) : IncludeEntry list =
        let parsed = semanticSnapshot snapshot

        let dslIncludes =
            PdxShaderSyntax.nodesOfKind ShaderNodeKind.IncludeFile parsed.syntax
            |> List.choose (fun node ->
                match node.name, node.nameSpan with
                | Some target, Some sourceSpan ->
                    let quoted = sourceSpan.Length >= 2
                    let start = sourceSpan.startOffset + (if quoted then 1 else 0)
                    let length = max 0 (sourceSpan.Length - (if quoted then 2 else 0))

                    Some
                        { target = target
                          start = start
                          length = length
                          condition = conditionAt start parsed.preprocessor }
                | _ -> None)

        let directiveIncludes =
            parsed.preprocessor.directives
            |> List.choose (fun directive ->
                if directive.kind <> PreprocessorDirectiveKind.Include then
                    None
                else
                    match unquoteIncludeArgument directive.argument with
                    | None -> None
                    | Some target ->
                        let relativeStart = directive.span.startOffset + snapshot.text.Substring(directive.span.startOffset, directive.span.Length).IndexOf(target, StringComparison.Ordinal)

                        Some
                            { target = target
                              start = max directive.span.startOffset relativeStart
                              length = target.Length
                              condition = directive.condition })

        (dslIncludes @ directiveIncludes)
        |> List.distinctBy (fun includeEntry -> includeEntry.start, includeEntry.target)
        |> List.sortBy _.start

    // Bounded include-extraction cache keyed by (canonical path, content hash).
    let private includeCacheCap = 512
    let private includeCache = BoundedLruCache<string * string, IncludeEntry list>(includeCacheCap)
    let private includeCacheLock = obj ()

    let extractIncludes (snapshot: ShaderSnapshot) : IncludeEntry list =
        let key = (snapshot.canonicalPath, snapshot.contentHash)

        lock includeCacheLock (fun () ->
            match includeCache.TryGet key with
            | Some entries -> entries
            | None ->
                let entries = extractIncludesRaw snapshot
                includeCache.Set(key, entries)
                entries)

    type ShaderProjectCacheStats =
        { semanticEntries: int
          semanticLimit: int
          includeEntries: int
          includeLimit: int }

    let cacheStats () =
        let semanticEntries = lock semanticCacheLock (fun () -> semanticCache.Count)
        let includeEntries = lock includeCacheLock (fun () -> includeCache.Count)
        { semanticEntries = semanticEntries
          semanticLimit = semanticCacheCap
          includeEntries = includeEntries
          includeLimit = includeCacheCap }

    let resetCaches () =
        lock semanticCacheLock (fun () -> semanticCache.Clear())
        lock includeCacheLock (fun () -> includeCache.Clear())

    /// Result of resolving one include target against the known snapshots.
    /// Resolved carries all snapshots for the target logical path, best origin first;
    /// Ambiguous carries every distinct file that matched (never silently pick one).
    type IncludeResolution =
        | Resolved of candidates: ShaderSnapshot list
        | Ambiguous of candidates: ShaderSnapshot list
        | Missing

    let private sortedDistinctByPath (snapshots: ShaderSnapshot list) =
        snapshots |> List.sortBy sortKey |> List.distinctBy _.canonicalPath

    let resolveInclude (snapshots: ShaderSnapshot list) (fromSnapshot: ShaderSnapshot) (includePath: string) : IncludeResolution =
        let byCanonicalPath target =
            let canonical = canonicalizePath target
            snapshots |> List.filter (fun s -> s.canonicalPath = canonical)

        let finish matches =
            match sortedDistinctByPath matches with
            | [] -> Missing
            | candidates -> Resolved candidates

        if Path.IsPathRooted includePath then
            finish (byCanonicalPath includePath)
        else
            let directory =
                Path.GetDirectoryName fromSnapshot.displayPath
                |> Option.ofObj
                |> Option.defaultValue ""

            let relativeMatches =
                byCanonicalPath (Path.Combine(directory, includePath))

            if not relativeMatches.IsEmpty then
                finish relativeMatches
            else
                let includeLogical = normalizeLogicalPath includePath

                let logicalMatches =
                    snapshots
                    |> List.filter (fun s ->
                        let logical = normalizeLogicalPath s.logicalPath
                        logical = includeLogical || logical.EndsWith("/" + includeLogical, StringComparison.Ordinal))

                let distinctLogicalPaths =
                    logicalMatches
                    |> List.map (fun s -> normalizeLogicalPath s.logicalPath)
                    |> List.distinct

                match distinctLogicalPaths with
                | [] -> Missing
                | [ _ ] -> finish logicalMatches
                | _ -> Ambiguous(sortedDistinctByPath logicalMatches)

    /// Include graph problem. Offsets point into the including file's original text.
    type IncludeProblem =
        | MissingInclude of includingPath: string * target: string * start: int * length: int
        | AmbiguousInclude of includingPath: string * target: string * start: int * length: int * candidates: string list
        | CyclicInclude of includingPath: string * target: string * start: int * length: int * cyclePath: string list
        | IncludeBudgetExceeded of includingPath: string * target: string * start: int * length: int * budget: string * limit: int

    type IncludeGraphEdge =
        { includingPath: string
          target: string
          resolvedPath: string option
          condition: PresenceCondition
          start: int
          length: int }

    /// Root snapshot plus every snapshot reachable through Includes.
    /// members: all reached snapshots (deduplicated, stable discovery order), including
    /// overridden lower-origin copies so definition lookup keeps them as candidates.
    /// effective: one snapshot per logical path, chosen by origin precedence.
    type CompileUnit =
        { root: ShaderSnapshot
          members: ShaderSnapshot list
          effective: ShaderSnapshot list
          problems: IncludeProblem list
          edges: IncludeGraphEdge list }

    let maxIncludeDepth = 256
    let maxCompileUnitMembers = 4096

    let private buildCompileUnitWhere includeCondition (snapshots: ShaderSnapshot list) (root: ShaderSnapshot) : CompileUnit =
        let visited = HashSet<string>(StringComparer.Ordinal)
        let members = ResizeArray<ShaderSnapshot>()
        let problems = ResizeArray<IncludeProblem>()
        let edges = ResizeArray<IncludeGraphEdge>()

        let tryAddMember (snapshot: ShaderSnapshot) =
            if visited.Contains snapshot.canonicalPath then
                struct (false, true)
            elif members.Count >= maxCompileUnitMembers then
                struct (false, false)
            else
                visited.Add snapshot.canonicalPath |> ignore
                members.Add snapshot
                struct (true, true)

        let addMemberBudgetProblem (snapshot: ShaderSnapshot) (includeEntry: IncludeEntry) =
            problems.Add(
                IncludeBudgetExceeded(
                    snapshot.displayPath,
                    includeEntry.target,
                    includeEntry.start,
                    includeEntry.length,
                    "members",
                    maxCompileUnitMembers
                )
            )

        let rec expand (snapshot: ShaderSnapshot) (ancestors: ShaderSnapshot list) =
            let stack = snapshot :: ancestors

            for includeEntry in extractIncludes snapshot |> List.filter (fun entry -> includeCondition entry.condition) do
                match resolveInclude snapshots snapshot includeEntry.target with
                | Resolved(best :: overridden) ->
                    edges.Add(
                        { includingPath = snapshot.displayPath
                          target = includeEntry.target
                          resolvedPath = Some best.displayPath
                          condition = includeEntry.condition
                          start = includeEntry.start
                          length = includeEntry.length }
                    )

                    if stack |> List.exists (fun item -> item.canonicalPath = best.canonicalPath) then
                        let chain =
                            best :: (stack |> List.takeWhile (fun item -> item.canonicalPath <> best.canonicalPath))

                        let cyclePath =
                            (chain |> List.rev |> List.map _.displayPath) @ [ best.displayPath ]

                        problems.Add(
                            CyclicInclude(snapshot.displayPath, includeEntry.target, includeEntry.start, includeEntry.length, cyclePath)
                        )
                    elif stack.Length >= maxIncludeDepth then
                        problems.Add(
                            IncludeBudgetExceeded(
                                snapshot.displayPath,
                                includeEntry.target,
                                includeEntry.start,
                                includeEntry.length,
                                "depth",
                                maxIncludeDepth
                            )
                        )
                    else
                        // Reserve the effective target before overridden definition
                        // candidates, so a hostile number of shadow copies cannot
                        // starve the actual include graph.
                        let struct (bestWasAdded, bestWithinBudget) = tryAddMember best
                        let mutable memberBudgetExceeded = not bestWithinBudget

                        // Overridden copies stay as definition candidates but are not expanded.
                        for copy in overridden do
                            let struct (_, copyWithinBudget) = tryAddMember copy
                            if not copyWithinBudget then memberBudgetExceeded <- true

                        if memberBudgetExceeded then addMemberBudgetProblem snapshot includeEntry
                        if bestWasAdded then expand best stack
                | Resolved [] -> ()
                | Ambiguous candidates ->
                    edges.Add(
                        { includingPath = snapshot.displayPath
                          target = includeEntry.target
                          resolvedPath = None
                          condition = includeEntry.condition
                          start = includeEntry.start
                          length = includeEntry.length }
                    )
                    problems.Add(
                        AmbiguousInclude(
                            snapshot.displayPath,
                            includeEntry.target,
                            includeEntry.start,
                            includeEntry.length,
                            candidates |> List.map _.displayPath
                        )
                    )
                | Missing ->
                    edges.Add(
                        { includingPath = snapshot.displayPath
                          target = includeEntry.target
                          resolvedPath = None
                          condition = includeEntry.condition
                          start = includeEntry.start
                          length = includeEntry.length }
                    )
                    problems.Add(
                        MissingInclude(snapshot.displayPath, includeEntry.target, includeEntry.start, includeEntry.length)
                    )

        let struct (rootWasAdded, _) = tryAddMember root

        if rootWasAdded then
            expand root []

        let effective =
            members
            |> Seq.groupBy (fun s -> normalizeLogicalPath s.logicalPath)
            |> Seq.map (snd >> Seq.minBy sortKey)
            |> Seq.sortBy sortKey
            |> Seq.toList

        { root = root
          members = List.ofSeq members
          effective = effective
          problems = List.ofSeq problems
          edges = List.ofSeq edges }

    /// All satisfiable branches are retained for semantic and variant queries.
    let buildCompileUnit (snapshots: ShaderSnapshot list) (root: ShaderSnapshot) : CompileUnit =
        buildCompileUnitWhere (fun condition -> satisfiable condition <> ConditionFalse) snapshots root

    /// Active-view compile unit for one concrete platform/macro environment.
    let buildCompileUnitForEnvironment environment snapshots root =
        buildCompileUnitWhere (fun condition -> evaluate environment condition <> ConditionFalse) snapshots root

    /// Reverse-dependency map: canonical path -> sorted canonical paths of snapshots that
    /// include it. Reserved for incremental invalidation.
    let reverseIncludeMap (snapshots: ShaderSnapshot list) : Map<string, string list> =
        snapshots
        |> List.collect (fun snapshot ->
            extractIncludes snapshot
            |> List.choose (fun includeEntry ->
                match resolveInclude snapshots snapshot includeEntry.target with
                | Resolved(best :: _) -> Some(best.canonicalPath, snapshot.canonicalPath)
                | _ -> None))
        |> List.groupBy fst
        |> List.map (fun (target, edges) -> target, edges |> List.map snd |> List.distinct |> List.sort)
        |> Map.ofList
