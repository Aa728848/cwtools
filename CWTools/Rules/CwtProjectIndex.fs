namespace CWTools.CwtLanguage

open System
open System.IO
open CWTools.Common
open CWTools.Process

/// Immutable project snapshot (handoff doc §4.5). `version` gates stale
/// rebuild results; `partial` reports capped/bounded indexing; `skippedFiles`
/// lists files dropped by the size bound.
type CwtProjectSnapshot =
    { version: int64
      documents: Map<string, CwtDocumentModel>
      symbols: Map<CwtSymbolKind, Map<string, CwtSymbol list>>
      diagnosticsByFile: Map<string, CwtDiagnostic list>
      /// Per-file single-document semantic diagnostics (Expression/Structure
      /// phases). Not published here (lint owns those) — they gate candidate
      /// activation.
      semanticDiagnosticsByFile: Map<string, CwtDiagnostic list>
      createdAt: DateTimeOffset
      partial: bool
      skippedFiles: string list
      /// Files that failed to parse (no document model; lint owns their
      /// syntax diagnostics). A non-empty list blocks rule activation.
      parseFailedFiles: string list }

/// Project-level aggregation and cross-file analysis. Pure functions only —
/// the snapshot lifecycle (overlay, rebuild tasks, version publication) lives
/// in src/Main.
module CwtProjectIndex =

    // ------------------------------------------------------------- paths

    /// Normalises a path for indexing: forward slashes, no trailing slash,
    /// case-folded on Windows (case-sensitive elsewhere).
    let normalizePath (path: string) =
        let normalized = path.Replace('\\', '/').TrimEnd('/')
        if OperatingSystem.IsWindows() then normalized.ToLowerInvariant() else normalized

    /// True when `candidate` is `root` or below it (both normalised).
    let isPathWithin (root: string) (candidate: string) =
        let r = normalizePath root
        let c = normalizePath candidate
        c = r || c.StartsWith(r + "/", StringComparison.Ordinal)

    /// Default bounds (Phase 3 safety: bounded caches, explicit partial state).
    let defaultMaxFiles = 2000
    let defaultMaxFileSizeBytes = 5_000_000L

    /// Resolves an `## inject` source path against a rule root. Rejects
    /// absolute paths and `..` traversal via GetFullPath + containment.
    /// Symlinked files are resolved to their real target before the check.
    let tryResolveInjectSource (ruleRoot: string) (sourcePath: string) =
        try
            let joined = Path.GetFullPath(Path.Combine(ruleRoot, sourcePath))
            let fi = FileInfo(joined)
            let resolved =
                if fi.Exists && fi.LinkTarget <> null then
                    let target = fi.ResolveLinkTarget(true)
                    if target <> null then target.FullName else joined
                else
                    joined
            if isPathWithin ruleRoot resolved then Some resolved else None
        with _ -> None

    // ------------------------------------------------------------ symbols

    let private emptySymbolIndex : Map<CwtSymbolKind, Map<string, CwtSymbol list>> = Map.empty

    let private addSymbol (index: Map<CwtSymbolKind, Map<string, CwtSymbol list>>) (s: CwtSymbol) =
        let byName = index |> Map.tryFind s.kind |> Option.defaultValue Map.empty
        let existing = byName |> Map.tryFind s.name |> Option.defaultValue []
        index |> Map.add s.kind (byName |> Map.add s.name (existing @ [ s ]))

    /// Builds the symbol index from document models.
    let buildSymbolIndex (documents: Map<string, CwtDocumentModel>) =
        documents
        |> Map.toSeq
        |> Seq.collect (fun (_, doc) -> doc.symbols)
        |> Seq.fold addSymbol emptySymbolIndex

    let symbolsOfKind (index: Map<CwtSymbolKind, Map<string, CwtSymbol list>>) kind =
        index |> Map.tryFind kind |> Option.defaultValue Map.empty

    // --------------------------------------------------------- diagnostics

    /// Built-in type names that need no project definition.
    let private builtInTypeNames = set [ "target"; "modifier" ]

    /// Enum references resolve against enum AND complex_enum definitions
    /// (Stellaris config references complex_enum counters via enum[...]).
    let private enumDefined (index: Map<CwtSymbolKind, Map<string, CwtSymbol list>>) (name: string) =
        (symbolsOfKind index CwtSymbolKind.CwtEnum).ContainsKey name
        || (symbolsOfKind index CwtSymbolKind.CwtComplexEnum).ContainsKey name

    let private isDefined (index: Map<CwtSymbolKind, Map<string, CwtSymbol list>>) (r: CwtReference) =
        match r.kind with
        | CwtSymbolKind.CwtEnum
        | CwtSymbolKind.CwtComplexEnum -> enumDefined index r.name
        | CwtSymbolKind.CwtType ->
            match r.name.Split('.') with
            | [| key; sub |] ->
                (symbolsOfKind index CwtSymbolKind.CwtType).ContainsKey key
                && (symbolsOfKind index CwtSymbolKind.CwtSubtype).ContainsKey sub
            | _ ->
                (symbolsOfKind index CwtSymbolKind.CwtType).ContainsKey r.name
                || builtInTypeNames.Contains r.name
        | CwtSymbolKind.CwtScope -> (symbolsOfKind index CwtSymbolKind.CwtScope).ContainsKey r.name
        | CwtSymbolKind.CwtScopeGroup -> (symbolsOfKind index CwtSymbolKind.CwtScopeGroup).ContainsKey r.name
        // Value sets are mostly built-in game sets; only flag when the
        // project itself defines value sets and the name is absent.
        | CwtSymbolKind.CwtValueSet ->
            (symbolsOfKind index CwtSymbolKind.CwtValueSet).IsEmpty
            || (symbolsOfKind index CwtSymbolKind.CwtValueSet).ContainsKey r.name
        | _ -> true

    let private kindHasProjectDefinitions (index: Map<CwtSymbolKind, Map<string, CwtSymbol list>>) (r: CwtReference) =
        match r.kind with
        | CwtSymbolKind.CwtEnum
        | CwtSymbolKind.CwtComplexEnum ->
            not ((symbolsOfKind index CwtSymbolKind.CwtEnum).IsEmpty)
            || not ((symbolsOfKind index CwtSymbolKind.CwtComplexEnum).IsEmpty)
        | CwtSymbolKind.CwtType -> not ((symbolsOfKind index CwtSymbolKind.CwtType).IsEmpty)
        | CwtSymbolKind.CwtScope -> not ((symbolsOfKind index CwtSymbolKind.CwtScope).IsEmpty)
        | CwtSymbolKind.CwtScopeGroup -> not ((symbolsOfKind index CwtSymbolKind.CwtScopeGroup).IsEmpty)
        | _ -> false

    let private projectDiagnostic code severity messageKey args range =
        { code = code
          severity = severity
          messageKey = messageKey
          messageArgs = args
          range = range
          phase = CwtDiagnosticPhase.Project
          related = [] }

    /// Undefined-reference diagnostics (CWT301). Only reported for kinds the
    /// project itself defines, which keeps built-in game-side symbols
    /// (scripted enums, flags, external types) silent.
    let private undefinedReferenceDiagnostics
        (index: Map<CwtSymbolKind, Map<string, CwtSymbol list>>)
        (documents: Map<string, CwtDocumentModel>)
        =
        documents
        |> Map.toSeq
        |> Seq.collect (fun (filePath, doc) ->
            doc.references
            |> Seq.filter (fun r -> kindHasProjectDefinitions index r && not (isDefined index r))
            |> Seq.map (fun r ->
                filePath, projectDiagnostic "CWT301" Severity.Warning "cwt.undefinedReference" [ r.name ] r.range))
        |> Seq.toList

    /// Same-file duplicate type declarations (CWT302). Duplicate enums,
    /// aliases and subtypes are legitimate multi-rule patterns in CWT and are
    /// not reported.
    let private duplicateTypeDiagnostics (documents: Map<string, CwtDocumentModel>) =
        documents
        |> Map.toSeq
        |> Seq.collect (fun (filePath, doc) ->
            doc.symbols
            |> List.filter (fun s -> s.kind = CwtSymbolKind.CwtType)
            |> List.groupBy (fun s -> s.name)
            |> List.filter (fun (_, group) -> group.Length > 1)
            |> Seq.collect (fun (name, group) ->
                let related = group |> List.skip 1 |> List.map (fun s -> (name, s.range))
                group
                |> Seq.map (fun s ->
                    filePath,
                    { projectDiagnostic "CWT302" Severity.Error "cwt.duplicateType" [ name ] s.range with
                        related = related })))
        |> Seq.toList

    /// Inject cycle detection (CWT401): a `## inject` chain that loops back.
    let private injectCycleDiagnostics (ruleRoot: string) (documents: Map<string, CwtDocumentModel>) =
        let edges =
            documents
            |> Map.toSeq
            |> Seq.collect (fun (filePath, doc) ->
                doc.injects
                |> Seq.choose (fun (sourcePath, _, range) ->
                    tryResolveInjectSource ruleRoot sourcePath
                    |> Option.bind (fun resolved ->
                        let key = normalizePath resolved
                        if documents.ContainsKey key then Some(filePath, key, range) else None)))
            |> Seq.toList

        let outgoing =
            edges
            |> List.groupBy (fun (from, _, _) -> normalizePath from)
            |> Map.ofList

        let rec hasCycle (current: string) (path: string list) (visited: Set<string>) =
            let key = normalizePath current
            if List.contains key path then true
            elif visited.Contains key then false
            else
                let next =
                    outgoing |> Map.tryFind key |> Option.map (List.map (fun (_, to_, _) -> to_)) |> Option.defaultValue []
                next |> List.exists (fun n -> hasCycle n (key :: path) (visited.Add key))

        edges
        |> Seq.filter (fun (_, target, _) -> hasCycle target [] Set.empty)
        |> Seq.map (fun (from, target, range) ->
            from, projectDiagnostic "CWT401" Severity.Error "cwt.injectCycle" [ target ] range)
        |> Seq.toList

    // ------------------------------------------------------------- build

    /// Builds an immutable snapshot from (filePath, text) pairs. Files are
    /// processed in normalised-path order for deterministic output; parse
    /// failures are excluded from the model (lint owns syntax diagnostics).
    let buildSnapshot
        (version: int64)
        (maxFiles: int)
        (maxFileSizeBytes: int64)
        (ruleRoot: string)
        (files: (string * string) list)
        : CwtProjectSnapshot =
        let ordered = files |> List.sortBy (fun (p, _) -> normalizePath p)
        let bounded = ordered |> List.truncate maxFiles
        let mutable skipped = []
        let mutable parseFailed = []

        let parsedDocuments =
            bounded
            |> List.choose (fun (filePath, text) ->
                if int64 text.Length > maxFileSizeBytes then
                    skipped <- filePath :: skipped
                    None
                else
                    match CwtLanguageService.parseFile filePath text with
                    | CwtLanguageService.ParseError _ ->
                        parseFailed <- filePath :: parseFailed
                        None
                    | CwtLanguageService.ParseOk root ->
                        let model =
                            { filePath = filePath
                              symbols = CwtLanguageService.collectSymbols filePath root
                              rootBlockNames =
                                root.AllArray
                                |> Array.toList
                                |> List.choose (function
                                    | NodeC n -> Some n.Key
                                    | LeafC l -> Some l.Key
                                    | _ -> None)
                                |> List.filter (fun k ->
                                    not (k.StartsWith("alias[") || k.StartsWith("single_alias[")))
                                |> List.distinct
                              references = CwtLanguageService.referencesInDocument filePath root
                              completionArguments = CwtLanguageService.completionArgumentsInDocument root
                              injects = CwtLanguageService.injectReferencesInDocument filePath root }

                        Some(filePath, model))

        // Map keys are normalised so cross-file lookups (inject resolution,
        // diagnostics, navigation) match regardless of case on Windows.
        let documents =
            parsedDocuments
            |> List.map (fun (p, model) -> normalizePath p, model)
            |> Map.ofList
        let index = buildSymbolIndex documents

        // Single-document semantic diagnostics gate activation; they are NOT
        // published from here (lint publishes them per document).
        let semanticByFile =
            parsedDocuments
            |> List.choose (fun (filePath, _) ->
                match CwtLanguageService.parseFile filePath (files |> List.tryFind (fun (p, _) -> normalizePath p = normalizePath filePath) |> Option.map snd |> Option.defaultValue "") with
                | CwtLanguageService.ParseError _ -> None
                | CwtLanguageService.ParseOk root ->
                    let diags = CwtLanguageService.analyzeRootPublic filePath root
                    Some(normalizePath filePath, diags))
            |> Map.ofList

        let allByFile =
            undefinedReferenceDiagnostics index documents
            @ duplicateTypeDiagnostics documents
            @ injectCycleDiagnostics ruleRoot documents
            |> List.groupBy (fun (filePath, _) -> normalizePath filePath)
            |> Map.ofList
            |> Map.map (fun _ entries -> entries |> List.map snd |> List.distinct)

        { version = version
          documents = documents
          symbols = index
          diagnosticsByFile = allByFile
          semanticDiagnosticsByFile = semanticByFile
          createdAt = DateTimeOffset.UtcNow
          partial = files.Length > maxFiles
          skippedFiles = skipped
          parseFailedFiles = parseFailed |> List.sortBy normalizePath }

    /// Per-file view of project diagnostics for a snapshot.
    let projectDiagnosticsForFile (snapshot: CwtProjectSnapshot) (filePath: string) =
        snapshot.diagnosticsByFile
        |> Map.tryFind (normalizePath filePath)
        |> Option.defaultValue []
