namespace CWTools.Games

open System
open System.Collections.Generic
open System.IO
open FSharp.Data
open CWTools.Utilities.Position

/// Effect runtime reachability for the Paradox FX shader DSL.
///
/// An Effect name is potentially engine ABI, so this module never treats "no textual
/// caller" as dead code. Every declared Effect is classified from conservative
/// evidence only, in the priority order of the support plan (section 8.4):
/// data_explicit > effect_file_convention > effect_file_convention_candidate >
/// engine_hardcoded > engine_or_unreferenced. EffectFileConvention requires an
/// exact, version-matching renderer contract; a plain effectFile selection remains
/// a Candidate. EngineHardcoded likewise requires a curated, version-matching ABI
/// catalog entry - absence of a textual reference is never enough.
/// engine_or_unreferenced is informational, never an error.
module PdxShaderRuntime =

    /// How a data file invokes the shader runtime.
    type ShaderCallKind =
        /// shader = EffectName
        | ShaderAssignment
        /// effectFile = "path.shader"
        | EffectFileSelection

    /// One located call site in a .gfx/.asset script file.
    type ShaderCallEvidence =
        { kind: ShaderCallKind
          /// Effect name or shader file path exactly as written.
          value: string
          sourceFile: string
          logicalPath: string
          origin: PdxShaderProject.ShaderOrigin
          /// Range of the value token (effect name / file path) in the source file.
          span: range
          /// Innermost enclosing block key (e.g. spriteType) when known.
          enclosingBlock: string option
          /// Name of the containing interface sprite when this is an effectFile
          /// selection inside a recognized sprite renderer block.
          interfaceSprite: string option
          /// Stable renderer subtype (normal, progress_bar, cornered_tile, ...).
          rendererSubtype: string option }

    /// One renderer input declared directly on an interface sprite block. Nested
    /// animation inputs are intentionally excluded until their renderer contract is
    /// versioned and understood.
    type InterfaceSpriteInput =
        { field: string
          value: string
          span: range }

    /// A named interface sprite selecting a shader file. This is a file-selection
    /// fact only; it does not prove that every Effect in the file is reachable.
    type InterfaceSpriteInvocation =
        { spriteName: string option
          rendererType: string
          rendererSubtype: string
          shaderFile: string
          sourceFile: string
          logicalPath: string
          origin: PdxShaderProject.ShaderOrigin
          shaderFileSpan: range
          blockRange: range
          resourceInputs: InterfaceSpriteInput list
          frameCount: int option }

    /// One textual `.gui` use of a GFX sprite. Absence of these uses is not proof
    /// that the sprite is unused because the executable can select sprites by name.
    type GuiSpriteUse =
        { spriteName: string
          sourceFile: string
          logicalPath: string
          origin: PdxShaderProject.ShaderOrigin
          span: range
          enclosingBlock: string option }

    /// Versioned renderer ABI for interface sprite effectFile selection. Unlike a
    /// plain file reference, this contract names only the Effect entry points the
    /// executable renderer selects for one subtype.
    type SpriteRendererContract =
        { game: string
          gameVersion: string
          rendererSubtype: string
          shaderFile: string
          effects: string list
          requiredInputs: string list
          evidence: string
          stale: bool
          notes: string option }

    /// Evidence behind a curated ABI catalog entry.
    type AbiEvidenceKind =
        | ManualRuntimeTest
        | ExecutableObservation
        | OfficialVanillaContract
        | AutomaticInventory

    /// Rename permission recorded in the ABI catalog.
    type AbiRenamePolicy =
        | CatalogForbidden
        | CatalogAllowed

    /// One curated engine-entry fact. Entries whose gameVersion does not match the
    /// version under analysis are loaded with stale = true and never classify Effects.
    type AbiCatalogEntry =
        { game: string
          gameVersion: string
          entryKind: string
          name: string
          shaderFile: string option
          evidence: AbiEvidenceKind
          renamePolicy: AbiRenamePolicy
          stale: bool
          notes: string option }

    type AbiCatalogDiagnostic =
        { code: string
          source: string
          entryIndex: int option
          message: string }

    type AbiCatalogUpgradeAudit =
        { fromVersion: string
          toVersion: string
          added: string list
          removed: string list
          retained: string list
          changed: string list
          diagnostics: AbiCatalogDiagnostic list }

    /// Versioned record proving that the ABI candidate universe was reviewed.
    /// It never promotes Effects; only matching entries in AbiCatalogEntry can do so.
    type ShaderAbiAudit =
        { game: string
          gameVersion: string
          reviewStatus: string
          automaticPromotion: bool
          shaderFileCount: int
          effectDeclarationCount: int
          uniqueEffectNameCount: int
          inventorySha256: string
          confirmedEngineEntries: string list
          stale: bool
          notes: string option }

    type ShaderAbiAuditVerification =
        { status: string
          source: string option
          gameVersion: string
          reviewStatus: string option
          automaticPromotion: bool
          shaderFileCount: int option
          modelVanillaShaderFiles: int
          auditedEffectDeclarations: int option
          auditedUniqueEffectNames: int option
          modelVanillaEffectDeclarations: int
          modelVanillaUniqueEffectNames: int
          confirmedEngineEntryCount: int
          activeCatalogEntryCount: int
          corpusMatches: bool
          diagnostics: AbiCatalogDiagnostic list }

    /// Highest-certainty reachability classification for one declared Effect.
    type EffectReachability =
        | DataExplicit of evidence: ShaderCallEvidence list
        /// Reserved: requires renderer-contract profile data that does not exist yet.
        | EffectFileConvention of evidence: ShaderCallEvidence list
        | EffectFileConventionCandidate of evidence: ShaderCallEvidence list
        | EngineHardcoded of entry: AbiCatalogEntry
        | EngineOrUnreferenced

    /// Safe-rename decision (plan section 8.5).
    type RenamePolicyDecision =
        | RenameAllowed of reason: string
        | RenameRequiresExplicitForce of reason: string
        | RenameDenied of reason: string

    /// Declared shader symbol kinds tracked by the runtime model.
    type ShaderDeclarationKind =
        | EffectDeclaration
        | VertexMainCodeDeclaration
        | PixelMainCodeDeclaration
        | GeometryMainCodeDeclaration
        | VertexStructDeclaration
        | ConstantBufferDeclaration
        | SamplerDeclaration
        | ShaderResourceDeclaration
        | HlslTypeDeclaration
        | HlslFunctionDeclaration
        | HlslVariableDeclaration
        | MacroDeclaration
        | BlendStateDeclaration
        | DepthStencilStateDeclaration
        | RasterizerStateDeclaration

    type ShaderDeclaration =
        { stableId: string
          name: string
          kind: ShaderDeclarationKind
          file: string
          logicalPath: string
          origin: PdxShaderProject.ShaderOrigin
          range: range
          selectionRange: range
          presenceCondition: string
          detail: string option }

    type ShaderSemanticReferenceKind =
        | EffectUsesVertexMainCode
        | EffectUsesPixelMainCode
        | EffectUsesGeometryMainCode
        | EffectUsesRenderState
        | MainCodeUsesConstantBuffer
        | HlslCallsFunction
        | HlslUsesSymbol
        | HlslUsesType
        | HlslUsesMember

    type ShaderSemanticReference =
        { sourceId: string option
          sourceName: string option
          targetName: string
          targetIds: string list
          kind: ShaderSemanticReferenceKind
          file: string
          logicalPath: string
          origin: PdxShaderProject.ShaderOrigin
          span: range
          presenceCondition: string
          stage: string }

    /// One declared Effect plus its classification and complete evidence list.
    type EffectInfo =
        { declaration: ShaderDeclaration
          reachability: EffectReachability
          allEvidence: ShaderCallEvidence list }

    /// Immutable runtime model: declarations, call evidence and the active catalog.
    type ShaderRuntimeModel =
        { gameVersion: string
          snapshots: PdxShaderProject.ShaderSnapshot list
          declarations: ShaderDeclaration list
          semanticReferences: ShaderSemanticReference list
          effects: EffectInfo list
          evidence: ShaderCallEvidence list
          interfaceSprites: InterfaceSpriteInvocation list
          guiSpriteUses: GuiSpriteUse list
          rendererContracts: SpriteRendererContract list
          catalog: AbiCatalogEntry list
          staleCatalogCount: int
          scriptFilesScanned: int
          scriptFilesSkipped: int }

    type AbiCandidate =
        { name: string
          shaderFile: string
          classification: string
          reviewReason: string }

    /// Text of one .gfx/.asset script file used for evidence extraction.
    type ScriptSource =
        { filepath: string
          logicalpath: string
          scope: string
          text: string }

    let createScriptSource filepath logicalpath scope text : ScriptSource =
        { filepath = filepath
          logicalpath = logicalpath
          scope = scope
          text = text }

    let mutable private vanillaShaderSourceCache: ScriptSource list = []
    let setVanillaShaderSources sources = vanillaShaderSourceCache <- sources
    let vanillaShaderSources () = vanillaShaderSourceCache

    let isEvidenceScriptFile (path: string) =
        let extension = Path.GetExtension(path)

        extension.Equals(".gfx", StringComparison.OrdinalIgnoreCase)
        || extension.Equals(".asset", StringComparison.OrdinalIgnoreCase)

    let private isGuiScriptFile (path: string) =
        Path.GetExtension(path).Equals(".gui", StringComparison.OrdinalIgnoreCase)

    // ------------------------------------------------------------------
    // Evidence extraction from .gfx/.asset script text
    // ------------------------------------------------------------------

    let private isEscapedQuote (text: string) index =
        let mutable slashCount = 0
        let mutable i = index - 1

        while i >= 0 && text[i] = '\\' do
            slashCount <- slashCount + 1
            i <- i - 1

        slashCount % 2 = 1

    type private RawAssignment =
        { kind: ShaderCallKind
          value: string
          keyStart: int
          valueStart: int
          valueLength: int }

    type private RawScalarAssignment =
        { key: string
          value: string
          quoted: bool
          keyStart: int
          valueStart: int
          valueLength: int }

    let private isIdentifierStart value = Char.IsLetter value || value = '_'

    let private isIdentifierPart value = Char.IsLetterOrDigit value || value = '_'

    let private isUnquotedScalarPart value =
        Char.IsLetterOrDigit value
        || value = '_'
        || value = '.'
        || value = '/'
        || value = ':'
        || value = '\\'
        || value = '-'

    /// Lossless-enough Clausewitz scalar assignment scanner for runtime evidence.
    /// `cleanDslText` has already blanked comments. This scanner, unlike the retired
    /// regex path, tracks quoted strings and escaped quotes directly and therefore
    /// cannot manufacture assignments from string contents or longer key names.
    /// Complex values (`{`, operators, scripted clauses) are deliberately skipped.
    let private scalarAssignments (cleaned: string) : RawScalarAssignment list =
        let assignments = ResizeArray<RawScalarAssignment>()
        let mutable i = 0

        let skipWhitespace () =
            while i < cleaned.Length && Char.IsWhiteSpace cleaned[i] do
                i <- i + 1

        let skipQuotedString () =
            if i < cleaned.Length && cleaned[i] = '"' then
                i <- i + 1

                while i < cleaned.Length && (cleaned[i] <> '"' || isEscapedQuote cleaned i) do
                    i <- i + 1

                if i < cleaned.Length then i <- i + 1

        while i < cleaned.Length do
            if cleaned[i] = '"' then
                skipQuotedString ()
            elif isIdentifierStart cleaned[i] then
                let keyStart = i
                i <- i + 1

                while i < cleaned.Length && isIdentifierPart cleaned[i] do
                    i <- i + 1

                let keyEnd = i
                skipWhitespace ()

                if i < cleaned.Length && cleaned[i] = '=' then
                    i <- i + 1
                    skipWhitespace ()

                    if i < cleaned.Length && cleaned[i] = '"' then
                        i <- i + 1
                        let valueStart = i

                        while i < cleaned.Length && (cleaned[i] <> '"' || isEscapedQuote cleaned i) do
                            i <- i + 1

                        let valueEnd = i

                        // Unterminated strings cannot provide reliable evidence.
                        if i < cleaned.Length then
                            assignments.Add
                                { key = cleaned.Substring(keyStart, keyEnd - keyStart)
                                  value = cleaned.Substring(valueStart, valueEnd - valueStart)
                                  quoted = true
                                  keyStart = keyStart
                                  valueStart = valueStart
                                  valueLength = valueEnd - valueStart }

                            i <- i + 1
                    elif i < cleaned.Length && isUnquotedScalarPart cleaned[i] then
                        let valueStart = i

                        while i < cleaned.Length && isUnquotedScalarPart cleaned[i] do
                            i <- i + 1

                        assignments.Add
                            { key = cleaned.Substring(keyStart, keyEnd - keyStart)
                              value = cleaned.Substring(valueStart, i - valueStart)
                              quoted = false
                              keyStart = keyStart
                              valueStart = valueStart
                              valueLength = i - valueStart }
                else
                    i <- max (keyStart + 1) keyEnd
            else
                i <- i + 1

        List.ofSeq assignments

    /// Innermost enclosing block key for each requested offset (offsets sorted).
    /// Tracks a brace stack; block headers follow the Clausewitz `key = {` shape.
    let private enclosingBlocks (cleaned: string) (offsets: int array) : (int * string option) list =
        let results = ResizeArray<int * string option>()
        let stack = Stack<string option>()
        let mutable inString = false
        let mutable i = 0
        let mutable next = 0

        let headerKey (braceIndex: int) =
            let mutable j = braceIndex - 1

            let skipWhitespace () =
                while j >= 0 && Char.IsWhiteSpace cleaned[j] do
                    j <- j - 1

            skipWhitespace ()

            if j >= 0 && cleaned[j] = '=' then
                j <- j - 1
                skipWhitespace ()
                let mutable nameEnd = j

                while j >= 0 && (Char.IsLetterOrDigit cleaned[j] || cleaned[j] = '_') do
                    j <- j - 1

                if nameEnd > j then
                    Some(cleaned.Substring(j + 1, nameEnd - j))
                else
                    None
            else
                None

        while i < cleaned.Length && next < offsets.Length do
            let target = offsets[next]

            if i = target then
                results.Add((target, (if stack.Count > 0 then stack.Peek() else None)))
                next <- next + 1
            else
                match cleaned[i] with
                | '"' when not (isEscapedQuote cleaned i) -> inString <- not inString
                | '{' when not inString -> stack.Push(headerKey i)
                | '}' when not inString -> if stack.Count > 0 then stack.Pop() |> ignore
                | _ -> ()

                i <- i + 1

        while next < offsets.Length do
            results.Add((offsets[next], (if stack.Count > 0 then stack.Peek() else None)))
            next <- next + 1

        List.ofSeq results

    let private collectAssignments (cleaned: string) : (RawAssignment * string option) list =
        let ordered =
            scalarAssignments cleaned
            |> List.choose (fun assignment ->
                let kind =
                    if assignment.key.Equals("shader", StringComparison.OrdinalIgnoreCase)
                       && (assignment.quoted
                           || (not (String.IsNullOrEmpty assignment.value)
                               && isIdentifierStart assignment.value[0]
                               && (assignment.value |> Seq.forall isIdentifierPart)))
                    then
                        Some ShaderAssignment
                    elif assignment.key.Equals("effectFile", StringComparison.OrdinalIgnoreCase) && assignment.quoted then
                        Some EffectFileSelection
                    else
                        None

                kind
                |> Option.bind (fun assignmentKind ->
                    if String.IsNullOrEmpty assignment.value then
                        None
                    else
                        Some
                            { kind = assignmentKind
                              value = assignment.value
                              keyStart = assignment.keyStart
                              valueStart = assignment.valueStart
                              valueLength = assignment.valueLength }))
            |> List.sortBy (fun assignment -> assignment.valueStart)
            |> List.toArray

        let enclosing = enclosingBlocks cleaned (ordered |> Array.map (fun assignment -> assignment.valueStart)) |> Map.ofList

        [ for assignment in ordered do
              assignment, (enclosing |> Map.tryFind assignment.valueStart |> Option.flatten) ]

    type private RawBlock =
        { key: string option
          headerStart: int
          openOffset: int
          closeOffset: int }

    let private blockHeaderAt (cleaned: string) (braceIndex: int) =
        let mutable j = braceIndex - 1

        while j >= 0 && Char.IsWhiteSpace cleaned[j] do
            j <- j - 1

        if j < 0 || cleaned[j] <> '=' then
            None, braceIndex
        else
            j <- j - 1

            while j >= 0 && Char.IsWhiteSpace cleaned[j] do
                j <- j - 1

            let nameEnd = j

            while j >= 0 && (Char.IsLetterOrDigit cleaned[j] || cleaned[j] = '_') do
                j <- j - 1

            if nameEnd > j then
                Some(cleaned.Substring(j + 1, nameEnd - j)), j + 1
            else
                None, braceIndex

    /// Balanced block spans outside comments, embedded HLSL and string literals.
    /// Unterminated blocks conservatively extend to EOF.
    let private blockSpans (cleaned: string) : RawBlock list =
        let blocks = ResizeArray<RawBlock>()
        let stack = Stack<string option * int * int>()
        let mutable inString = false

        for i = 0 to cleaned.Length - 1 do
            match cleaned[i] with
            | '"' when not (isEscapedQuote cleaned i) -> inString <- not inString
            | '{' when not inString ->
                let key, headerStart = blockHeaderAt cleaned i
                stack.Push((key, headerStart, i))
            | '}' when not inString && stack.Count > 0 ->
                let key, headerStart, openOffset = stack.Pop()
                blocks.Add
                    { key = key
                      headerStart = headerStart
                      openOffset = openOffset
                      closeOffset = i + 1 }
            | _ -> ()

        while stack.Count > 0 do
            let key, headerStart, openOffset = stack.Pop()
            blocks.Add
                { key = key
                  headerStart = headerStart
                  openOffset = openOffset
                  closeOffset = cleaned.Length }

        blocks
        |> Seq.sortBy (fun block -> block.openOffset, -(block.closeOffset - block.openOffset))
        |> Seq.toList

    let private innermostBlockAt (blocks: RawBlock list) offset =
        blocks
        |> List.filter (fun block -> offset > block.openOffset && offset < block.closeOffset)
        |> List.sortBy (fun block -> block.closeOffset - block.openOffset)
        |> List.tryHead

    let private rendererSubtypeFor (blockKey: string) =
        match blockKey.ToLowerInvariant() with
        | "spritetype" -> Some "normal"
        | "corneredtilespritetype" -> Some "cornered_tile"
        | "flagspritetype" -> Some "flag_sprite"
        | "frameanimatedspritetype" -> Some "framed_animated_sprite"
        | "textspritetype" -> Some "text_sprite"
        | "progressbartype" -> Some "progress_bar"
        | "portraittype" -> Some "portrait"
        | _ -> None

    /// LSP-compatible range for a raw offset span (offsets as produced by the scanners).
    let offsetRange (filepath: string) (text: string) (startOffset: int) (length: int) =
        mkRange
            filepath
            (PdxShaderProject.posFromOffset text startOffset)
            (PdxShaderProject.posFromOffset text (startOffset + max 1 length))
    /// Extract `interface/*.gfx` sprite blocks that select a Shader file. Only
    /// direct scalar fields of the renderer block are attached as resource inputs;
    /// nested animation blocks remain separate until a renderer ABI profile exists.
    let extractInterfaceSpriteInvocationsFromText origin filepath logicalpath (text: string) : InterfaceSpriteInvocation list =
        if String.IsNullOrEmpty text then
            []
        else
            let cleaned = PdxShaderProject.cleanDslText text
            let blocks = blockSpans cleaned
            let scalars = scalarAssignments cleaned

            [ for block in blocks do
                  match block.key with
                  | Some rendererType ->
                    match rendererSubtypeFor rendererType with
                    | None -> ()
                    | Some subtype ->
                      let direct =
                          scalars
                          |> List.filter (fun scalar ->
                              scalar.valueStart > block.openOffset
                              && scalar.valueStart < block.closeOffset
                              && (innermostBlockAt blocks scalar.valueStart
                                  |> Option.exists (fun owner -> owner.openOffset = block.openOffset)))

                      let tryScalar key =
                          direct |> List.tryFind (fun scalar -> scalar.key.Equals(key, StringComparison.OrdinalIgnoreCase))

                      let spriteName =
                          tryScalar "name"
                          |> Option.map _.value
                          |> Option.filter (String.IsNullOrWhiteSpace >> not)

                      let inputs =
                          direct
                          |> List.filter (fun scalar ->
                              match scalar.key.ToLowerInvariant() with
                              | "texturefile"
                              | "texturefile1"
                              | "texturefile2"
                              | "masking_texture" -> true
                              | _ -> false)
                          |> List.map (fun scalar ->
                              { field = scalar.key
                                value = scalar.value
                                span = offsetRange filepath text scalar.valueStart scalar.valueLength })

                      let frameCount =
                          tryScalar "noOfFrames"
                          |> Option.bind (fun scalar ->
                              match Int32.TryParse scalar.value with
                              | true, value -> Some value
                              | false, _ -> None)

                      for effectFile in direct |> List.filter (fun scalar -> scalar.key.Equals("effectFile", StringComparison.OrdinalIgnoreCase)) do
                          yield
                              { spriteName = spriteName
                                rendererType = rendererType
                                rendererSubtype = subtype
                                shaderFile = effectFile.value
                                sourceFile = filepath
                                logicalPath = logicalpath
                                origin = origin
                                shaderFileSpan = offsetRange filepath text effectFile.valueStart effectFile.valueLength
                                blockRange = offsetRange filepath text block.headerStart (block.closeOffset - block.headerStart)
                                resourceInputs = inputs
                                frameCount = frameCount }
                  | None -> () ]

    /// Extract static `.gui` `spriteType = "GFX_*"` uses. Dynamic expressions are
    /// intentionally left unknown rather than fabricated as concrete edges.
    let extractGuiSpriteUsesFromText origin filepath logicalpath (text: string) : GuiSpriteUse list =
        if String.IsNullOrEmpty text then
            []
        else
            let cleaned = PdxShaderProject.cleanDslText text
            let assignments = scalarAssignments cleaned
            let enclosing =
                assignments
                |> List.map _.valueStart
                |> List.toArray
                |> enclosingBlocks cleaned
                |> Map.ofList

            assignments
            |> List.filter (fun scalar ->
                scalar.key.Equals("spriteType", StringComparison.OrdinalIgnoreCase)
                && scalar.value.StartsWith("GFX_", StringComparison.OrdinalIgnoreCase))
            |> List.map (fun scalar ->
                { spriteName = scalar.value
                  sourceFile = filepath
                  logicalPath = logicalpath
                  origin = origin
                  span = offsetRange filepath text scalar.valueStart scalar.valueLength
                  enclosingBlock = enclosing |> Map.tryFind scalar.valueStart |> Option.flatten })

    let private interfaceSpriteCacheCap = 2048
    let private interfaceSpriteCache = Dictionary<string * string * string * PdxShaderProject.ShaderOrigin, InterfaceSpriteInvocation list>()
    let private interfaceSpriteCacheLock = obj ()

    let private extractInterfaceSpriteInvocationsCached origin filepath logicalpath text =
        let key =
            PdxShaderProject.canonicalizePath filepath,
            PdxShaderProject.contentHashForText text,
            PdxShaderProject.normalizeLogicalPath logicalpath,
            origin

        lock interfaceSpriteCacheLock (fun () ->
            match interfaceSpriteCache.TryGetValue key with
            | true, invocations -> invocations
            | _ ->
                let invocations = extractInterfaceSpriteInvocationsFromText origin filepath logicalpath text
                if interfaceSpriteCache.Count >= interfaceSpriteCacheCap then interfaceSpriteCache.Clear()
                interfaceSpriteCache[key] <- invocations
                invocations)

    let private guiSpriteUseCacheCap = 4096
    let private guiSpriteUseCache = Dictionary<string * string * string * PdxShaderProject.ShaderOrigin, GuiSpriteUse list>()
    let private guiSpriteUseCacheLock = obj ()

    let private extractGuiSpriteUsesCached origin filepath logicalpath text =
        let key =
            PdxShaderProject.canonicalizePath filepath,
            PdxShaderProject.contentHashForText text,
            PdxShaderProject.normalizeLogicalPath logicalpath,
            origin

        lock guiSpriteUseCacheLock (fun () ->
            match guiSpriteUseCache.TryGetValue key with
            | true, uses -> uses
            | _ ->
                let uses = extractGuiSpriteUsesFromText origin filepath logicalpath text
                if guiSpriteUseCache.Count >= guiSpriteUseCacheCap then guiSpriteUseCache.Clear()
                guiSpriteUseCache[key] <- uses
                uses)

    /// Extract shader call evidence from one .gfx/.asset source text.
    /// Comment, preprocessor and string contents never produce evidence.
    let extractEvidenceFromText origin (filepath: string) logicalpath (text: string) : ShaderCallEvidence list =
        if String.IsNullOrEmpty text then
            []
        else
            let cleaned = PdxShaderProject.cleanDslText text

            let interfaceSprites =
                if Path.GetExtension(filepath).Equals(".gfx", StringComparison.OrdinalIgnoreCase) then
                    extractInterfaceSpriteInvocationsCached origin filepath logicalpath text
                else
                    []

            [ for (assignment, enclosing) in collectAssignments cleaned do
                  let sprite =
                      if assignment.kind = EffectFileSelection then
                          interfaceSprites
                          |> List.tryFind (fun candidate -> candidate.shaderFileSpan = offsetRange filepath text assignment.valueStart assignment.valueLength)
                      else
                          None

                  { kind = assignment.kind
                    value = assignment.value
                    sourceFile = filepath
                    logicalPath = logicalpath
                    origin = origin
                    span = offsetRange filepath text assignment.valueStart assignment.valueLength
                    enclosingBlock = enclosing
                    interfaceSprite = sprite |> Option.bind _.spriteName
                    rendererSubtype = sprite |> Option.map _.rendererSubtype } ]

    // Bounded evidence cache includes logical path and origin because both are
    // returned as provenance even when the physical file contents stay unchanged.
    let private evidenceCacheCap = 2048
    let private evidenceCache = Dictionary<string * string * string * PdxShaderProject.ShaderOrigin, ShaderCallEvidence list>()
    let private evidenceCacheLock = obj ()

    let private extractEvidenceCached (source: ScriptSource) =
        let hash = PdxShaderProject.contentHashForText source.text
        let origin = PdxShaderProject.originForResource source.scope source.filepath
        let key =
            PdxShaderProject.canonicalizePath source.filepath,
            hash,
            PdxShaderProject.normalizeLogicalPath source.logicalpath,
            origin

        lock evidenceCacheLock (fun () ->
            match evidenceCache.TryGetValue key with
            | true, evidence -> evidence
            | _ ->
                let evidence = extractEvidenceFromText origin source.filepath source.logicalpath source.text
                if evidenceCache.Count >= evidenceCacheCap then evidenceCache.Clear()
                evidenceCache[key] <- evidence
                evidence)

    // ------------------------------------------------------------------
    // ABI catalog (curated, versioned; empty by default)
    // ------------------------------------------------------------------

    let mutable private catalogEntries: AbiCatalogEntry list = []
    let mutable private catalogLoadedFrom: string option = None
    let mutable private catalogDiagnostics: AbiCatalogDiagnostic list = []

    let private stringProperty (json: JsonValue) name =
        match json.TryGetProperty name with
        | Some(JsonValue.String value) when not (String.IsNullOrWhiteSpace value) -> Some value
        | _ -> None

    let private parseEvidenceKind =
        function
        | "manual_runtime_test" -> Some ManualRuntimeTest
        | "executable_observation" -> Some ExecutableObservation
        | "official_vanilla_contract" -> Some OfficialVanillaContract
        | "automatic_inventory" -> Some AutomaticInventory
        | _ -> None

    let private catalogDiagnostic source entryIndex code message =
        { code = code
          source = source
          entryIndex = entryIndex
          message = message }

    /// Parse and validate the reviewed ABI input. Unknown object fields are forward
    /// compatible, but missing/unknown evidence never defaults to a trusted fact.
    let validateShaderAbiCatalogText (gameVersion: string option) (source: string) (text: string) =
        try
            let json = JsonValue.Parse text
            let diagnostics = ResizeArray<AbiCatalogDiagnostic>()
            let schema = stringProperty json "_schema"
            let rootGame = stringProperty json "game"

            if schema <> Some "cwtools/shader-abi-catalog/v1" then
                diagnostics.Add(catalogDiagnostic source None "CWFXABI001" "_schema must be cwtools/shader-abi-catalog/v1.")

            if rootGame.IsNone then
                diagnostics.Add(catalogDiagnostic source None "CWFXABI002" "Root game is required.")

            let values =
                match json.TryGetProperty "entries" with
                | Some(JsonValue.Array entries) -> entries
                | _ ->
                    diagnostics.Add(catalogDiagnostic source None "CWFXABI003" "entries must be an array.")
                    [||]

            let entries = ResizeArray<AbiCatalogEntry>()
            let seen = HashSet<string>(StringComparer.OrdinalIgnoreCase)

            for index in 0 .. values.Length - 1 do
                let entry = values[index]
                let entryDiagnostics = ResizeArray<AbiCatalogDiagnostic>()
                let required name code =
                    match stringProperty entry name with
                    | Some value -> Some value
                    | None ->
                        entryDiagnostics.Add(catalogDiagnostic source (Some index) code (sprintf "%s is required." name))
                        None
                let entryGame = required "game" "CWFXABI101"
                let entryVersion = required "game_version" "CWFXABI102"
                let entryKind = required "entry_kind" "CWFXABI103"
                let name = required "name" "CWFXABI104"
                let evidenceText = required "evidence" "CWFXABI105"
                let renameText = required "rename_policy" "CWFXABI106"

                match rootGame, entryGame with
                | Some expected, Some actual when not (expected.Equals(actual, StringComparison.OrdinalIgnoreCase)) ->
                    entryDiagnostics.Add(catalogDiagnostic source (Some index) "CWFXABI107" "Entry game must match the root game.")
                | _ -> ()

                match entryKind with
                | Some value when not (value.Equals("effect", StringComparison.OrdinalIgnoreCase)) ->
                    entryDiagnostics.Add(catalogDiagnostic source (Some index) "CWFXABI108" "entry_kind must be effect.")
                | _ -> ()

                let evidence = evidenceText |> Option.bind parseEvidenceKind
                if evidenceText.IsSome && evidence.IsNone then
                    entryDiagnostics.Add(catalogDiagnostic source (Some index) "CWFXABI109" "Unknown evidence; evidence must be manual_runtime_test, executable_observation, official_vanilla_contract, or automatic_inventory.")

                let renamePolicy =
                    match renameText |> Option.map _.ToLowerInvariant() with
                    | Some "forbidden" -> Some CatalogForbidden
                    | Some "allowed" -> Some CatalogAllowed
                    | Some _ ->
                        entryDiagnostics.Add(catalogDiagnostic source (Some index) "CWFXABI110" "rename_policy must be forbidden or allowed.")
                        None
                    | None -> None

                if entryDiagnostics.Count = 0 then
                    let entryVersion = entryVersion.Value
                    let stale =
                        match gameVersion with
                        | Some current -> not (entryVersion.Equals(current, StringComparison.OrdinalIgnoreCase))
                        | None -> true
                    let shaderFile = stringProperty entry "shader_file"
                    let key = sprintf "%s|%s|%s|%s" entryGame.Value entryVersion name.Value (defaultArg shaderFile "")

                    if seen.Add key then
                        entries.Add
                            { game = entryGame.Value
                              gameVersion = entryVersion
                              entryKind = entryKind.Value
                              name = name.Value
                              shaderFile = shaderFile
                              evidence = evidence.Value
                              renamePolicy = renamePolicy.Value
                              stale = stale
                              notes = stringProperty entry "notes" }
                    else
                        diagnostics.Add(catalogDiagnostic source (Some index) "CWFXABI111" "Duplicate ABI entry was ignored.")

                for diagnostic in entryDiagnostics do diagnostics.Add diagnostic

            if diagnostics |> Seq.exists (fun diagnostic -> diagnostic.entryIndex.IsNone) then
                [], List.ofSeq diagnostics
            else
                List.ofSeq entries, List.ofSeq diagnostics
        with ex ->
            [], [ catalogDiagnostic source None "CWFXABI000" (sprintf "Invalid JSON: %s" ex.Message) ]

    let loadShaderAbiCatalogFromText (gameVersion: string option) (source: string) (text: string) : unit =
        let entries, diagnostics = validateShaderAbiCatalogText gameVersion source text
        catalogEntries <- entries
        catalogDiagnostics <- diagnostics
        catalogLoadedFrom <- Some source

        for diagnostic in diagnostics do
            CWTools.Utilities.Utils.logWarning (sprintf "PdxShaderRuntime: %s: %s" diagnostic.code diagnostic.message)

    /// Load the curated ABI catalog from a JSON file. A missing file leaves the
    /// catalog empty; an unreadable file also fails closed to an empty catalog.
    let loadShaderAbiCatalog (gameVersion: string option) (path: string) : unit =
        if File.Exists path then
            try
                loadShaderAbiCatalogFromText gameVersion path (File.ReadAllText path)
            with ex ->
                catalogEntries <- []
                catalogLoadedFrom <- None
                catalogDiagnostics <- [ catalogDiagnostic path None "CWFXABI000" ex.Message ]

                CWTools.Utilities.Utils.logWarning (
                    sprintf "PdxShaderRuntime: failed to read shader ABI catalog %s: %s" path ex.Message
                )
        else
            catalogEntries <- []
            catalogLoadedFrom <- None
            catalogDiagnostics <- [ catalogDiagnostic path None "CWFXABI000" "Catalog file does not exist." ]

    let resetShaderAbiCatalog () =
        catalogEntries <- []
        catalogLoadedFrom <- None
        catalogDiagnostics <- []

    /// Catalog entries that may classify Effects (stale entries never do).
    let activeCatalog () = catalogEntries |> List.filter (fun entry -> not entry.stale)

    let catalogInfo () = catalogLoadedFrom, catalogEntries

    let shaderAbiCatalogDiagnostics () = catalogDiagnostics

    let auditShaderAbiCatalogUpgrade fromVersion fromText toVersion toText =
        let fromEntries, fromDiagnostics =
            validateShaderAbiCatalogText (Some fromVersion) (sprintf "ABI %s" fromVersion) fromText
        let toEntries, toDiagnostics =
            validateShaderAbiCatalogText (Some toVersion) (sprintf "ABI %s" toVersion) toText
        let key (entry: AbiCatalogEntry) =
            sprintf
                "%s|%s"
                (entry.name.ToLowerInvariant())
                (entry.shaderFile |> Option.defaultValue "" |> PdxShaderProject.normalizeLogicalPath)
        let fromMap = fromEntries |> List.map (fun entry -> key entry, entry) |> Map.ofList
        let toMap = toEntries |> List.map (fun entry -> key entry, entry) |> Map.ofList
        let fromKeys = fromMap |> Map.keys |> Set.ofSeq
        let toKeys = toMap |> Map.keys |> Set.ofSeq
        let display (keys: Set<string>) (map: Map<string, AbiCatalogEntry>) =
            keys |> Set.toList |> List.map (fun item -> map[item].name) |> List.sort
        let retainedKeys = Set.intersect fromKeys toKeys
        let changed =
            retainedKeys
            |> Set.toList
            |> List.choose (fun item ->
                let before = fromMap[item]
                let after = toMap[item]
                if before.evidence <> after.evidence || before.renamePolicy <> after.renamePolicy || before.notes <> after.notes then Some after.name else None)
            |> List.sort
        { fromVersion = fromVersion
          toVersion = toVersion
          added = display (Set.difference toKeys fromKeys) toMap
          removed = display (Set.difference fromKeys toKeys) fromMap
          retained = display retainedKeys toMap
          changed = changed
          diagnostics = fromDiagnostics @ toDiagnostics }

    // ------------------------------------------------------------------
    // ABI audit evidence (review coverage, never classification authority)
    // ------------------------------------------------------------------

    let mutable private abiAudit: ShaderAbiAudit option = None
    let mutable private abiAuditLoadedFrom: string option = None
    let mutable private abiAuditDiagnostics: AbiCatalogDiagnostic list = []

    let private nonNegativeIntProperty (json: JsonValue) name =
        match json.TryGetProperty name with
        | Some(JsonValue.Number value)
            when value = Decimal.Truncate value && value >= 0M && value <= decimal Int32.MaxValue -> Some(int value)
        | _ -> None

    let private boolProperty (json: JsonValue) name =
        match json.TryGetProperty name with
        | Some(JsonValue.Boolean value) -> Some value
        | _ -> None

    let private stringArrayProperty (json: JsonValue) name =
        match json.TryGetProperty name with
        | Some(JsonValue.Array values) ->
            values
            |> Array.choose (function
                | JsonValue.String value when not (String.IsNullOrWhiteSpace value) -> Some(value.Trim())
                | _ -> None)
            |> Array.toList
            |> Some
        | _ -> None

    /// Validate the versioned review artifact. `automatic_promotion` must be false:
    /// audit completion records coverage but can never manufacture ABI facts.
    let validateShaderAbiAuditText (gameVersion: string option) (source: string) (text: string) =
        try
            let json = JsonValue.Parse text
            let diagnostics = ResizeArray<AbiCatalogDiagnostic>()
            let requiredString name code =
                match stringProperty json name with
                | Some value -> Some value
                | None ->
                    diagnostics.Add(catalogDiagnostic source None code (sprintf "%s is required." name))
                    None

            if stringProperty json "_schema" <> Some "cwtools/shader-abi-audit/v1" then
                diagnostics.Add(catalogDiagnostic source None "CWFXABIA001" "_schema must be cwtools/shader-abi-audit/v1.")

            let game = requiredString "game" "CWFXABIA002"
            let auditedVersion = requiredString "game_version" "CWFXABIA003"
            let reviewStatus = requiredString "review_status" "CWFXABIA004"
            if reviewStatus |> Option.exists (fun value -> value <> "complete" && value <> "in_progress") then
                diagnostics.Add(catalogDiagnostic source None "CWFXABIA005" "review_status must be complete or in_progress.")

            let automaticPromotion = boolProperty json "automatic_promotion"
            match automaticPromotion with
            | Some false -> ()
            | Some true -> diagnostics.Add(catalogDiagnostic source None "CWFXABIA006" "automatic_promotion must be false; an audit cannot promote ABI entries.")
            | None -> diagnostics.Add(catalogDiagnostic source None "CWFXABIA006" "automatic_promotion must be the boolean false.")

            let candidateUniverse = json.TryGetProperty "candidate_universe"
            let requiredCount name code =
                match candidateUniverse |> Option.bind (fun value -> nonNegativeIntProperty value name) with
                | Some value -> Some value
                | None ->
                    diagnostics.Add(catalogDiagnostic source None code (sprintf "candidate_universe.%s must be a non-negative integer." name))
                    None
            let shaderFileCount = requiredCount "shader_files" "CWFXABIA101"
            let effectDeclarationCount = requiredCount "effect_declarations" "CWFXABIA102"
            let uniqueEffectNameCount = requiredCount "unique_effect_names" "CWFXABIA103"
            let inventorySha256 =
                candidateUniverse |> Option.bind (fun value -> stringProperty value "inventory_sha256")
            if inventorySha256 |> Option.exists (fun value ->
                not (System.Text.RegularExpressions.Regex.IsMatch(value, "^[0-9a-fA-F]{64}$")))
               || inventorySha256.IsNone then
                diagnostics.Add(catalogDiagnostic source None "CWFXABIA104" "candidate_universe.inventory_sha256 must be 64 hexadecimal characters.")

            let confirmedEngineEntries = stringArrayProperty json "confirmed_engine_entries"
            if confirmedEngineEntries.IsNone then
                diagnostics.Add(catalogDiagnostic source None "CWFXABIA201" "confirmed_engine_entries must be an array of reviewed catalog identities.")

            let reviewedStages = HashSet<string>(StringComparer.OrdinalIgnoreCase)
            match json.TryGetProperty "evidence_reviews" with
            | Some(JsonValue.Array reviews) ->
                for review in reviews do
                    match stringProperty review "stage", stringProperty review "status" with
                    | Some stage, Some status when status = "reviewed" || status = "no_qualifying_evidence" ->
                        reviewedStages.Add stage |> ignore
                    | _ -> diagnostics.Add(catalogDiagnostic source None "CWFXABIA301" "Each evidence review needs a stage and status reviewed/no_qualifying_evidence.")
            | _ -> diagnostics.Add(catalogDiagnostic source None "CWFXABIA300" "evidence_reviews must be an array.")

            if reviewStatus = Some "complete" then
                for requiredStage in
                    [ "vanilla_shader_inventory"
                      "textual_call_sites"
                      "renderer_contracts"
                      "executable_or_runtime" ] do
                    if not (reviewedStages.Contains requiredStage) then
                        diagnostics.Add(catalogDiagnostic source None "CWFXABIA302" (sprintf "Complete audit is missing evidence stage %s." requiredStage))

            if diagnostics.Count > 0 then
                None, List.ofSeq diagnostics
            else
                let auditedVersion = auditedVersion.Value
                let stale =
                    match gameVersion with
                    | Some current -> not (auditedVersion.Equals(current, StringComparison.OrdinalIgnoreCase))
                    | None -> true
                Some
                    { game = game.Value
                      gameVersion = auditedVersion
                      reviewStatus = reviewStatus.Value
                      automaticPromotion = automaticPromotion.Value
                      shaderFileCount = shaderFileCount.Value
                      effectDeclarationCount = effectDeclarationCount.Value
                      uniqueEffectNameCount = uniqueEffectNameCount.Value
                      inventorySha256 = inventorySha256.Value.ToLowerInvariant()
                      confirmedEngineEntries = confirmedEngineEntries.Value
                      stale = stale
                      notes = stringProperty json "notes" }, []
        with ex ->
            None, [ catalogDiagnostic source None "CWFXABIA000" (sprintf "Invalid JSON: %s" ex.Message) ]

    let loadShaderAbiAuditFromText (gameVersion: string option) (source: string) (text: string) =
        let parsed, diagnostics = validateShaderAbiAuditText gameVersion source text
        abiAudit <- parsed
        abiAuditLoadedFrom <- Some source
        abiAuditDiagnostics <- diagnostics
        for diagnostic in diagnostics do
            CWTools.Utilities.Utils.logWarning (sprintf "PdxShaderRuntime: %s: %s" diagnostic.code diagnostic.message)

    let loadShaderAbiAudit (gameVersion: string option) (path: string) =
        if File.Exists path then
            try
                loadShaderAbiAuditFromText gameVersion path (File.ReadAllText path)
            with ex ->
                abiAudit <- None
                abiAuditLoadedFrom <- Some path
                abiAuditDiagnostics <- [ catalogDiagnostic path None "CWFXABIA000" ex.Message ]
        else
            abiAudit <- None
            abiAuditLoadedFrom <- Some path
            abiAuditDiagnostics <- [ catalogDiagnostic path None "CWFXABIA000" "ABI audit file does not exist." ]

    let resetShaderAbiAudit () =
        abiAudit <- None
        abiAuditLoadedFrom <- None
        abiAuditDiagnostics <- []

    let shaderAbiAuditInfo () = abiAuditLoadedFrom, abiAudit, abiAuditDiagnostics

    let private abiIdentity (name: string) (shaderFile: string option) =
        sprintf "%s|%s" (name.ToLowerInvariant()) (shaderFile |> Option.defaultValue "" |> PdxShaderProject.normalizeLogicalPath)

    /// Compare the reviewed candidate-universe snapshot with the vanilla portion of
    /// the active model and with the curated catalog. A mismatch fails closed.
    let verifyShaderAbiAudit (model: ShaderRuntimeModel) =
        let vanillaShaderFiles =
            model.snapshots
            |> List.filter (fun snapshot ->
                snapshot.origin = PdxShaderProject.Vanilla
                && snapshot.logicalPath.EndsWith(".shader", StringComparison.OrdinalIgnoreCase))
            |> List.length
        let vanillaEffects =
            model.declarations
            |> List.filter (fun declaration ->
                declaration.kind = EffectDeclaration
                && declaration.origin = PdxShaderProject.Vanilla)
        let uniqueVanillaEffects =
            vanillaEffects
            |> List.map (fun declaration -> declaration.name.ToLowerInvariant())
            |> Set.ofList
            |> Set.count
        let activeEntries = activeCatalog ()
        let activeIdentities =
            activeEntries
            |> List.map (fun entry -> abiIdentity entry.name entry.shaderFile)
            |> Set.ofList
        let confirmedIdentities =
            abiAudit
            |> Option.map (fun audit -> audit.confirmedEngineEntries |> List.map _.ToLowerInvariant() |> Set.ofList)
            |> Option.defaultValue Set.empty
        let catalogMatches = activeIdentities = confirmedIdentities
        let corpusMatches =
            abiAudit
            |> Option.exists (fun audit ->
                audit.shaderFileCount = vanillaShaderFiles
                && audit.effectDeclarationCount = vanillaEffects.Length
                && audit.uniqueEffectNameCount = uniqueVanillaEffects)
        let status =
            match abiAudit with
            | None when not (List.isEmpty abiAuditDiagnostics) -> "invalid"
            | None -> "unavailable"
            | Some audit when audit.stale -> "stale"
            | Some audit when audit.reviewStatus <> "complete" -> "in_progress"
            | Some _ when vanillaShaderFiles = 0 -> "corpus_unavailable"
            | Some _ when not corpusMatches -> "corpus_mismatch"
            | Some _ when not catalogMatches -> "catalog_mismatch"
            | Some _ -> "current"
        { status = status
          source = abiAuditLoadedFrom
          gameVersion = model.gameVersion
          reviewStatus = abiAudit |> Option.map _.reviewStatus
          automaticPromotion = abiAudit |> Option.map _.automaticPromotion |> Option.defaultValue false
          shaderFileCount = abiAudit |> Option.map _.shaderFileCount
          modelVanillaShaderFiles = vanillaShaderFiles
          auditedEffectDeclarations = abiAudit |> Option.map _.effectDeclarationCount
          auditedUniqueEffectNames = abiAudit |> Option.map _.uniqueEffectNameCount
          modelVanillaEffectDeclarations = vanillaEffects.Length
          modelVanillaUniqueEffectNames = uniqueVanillaEffects
          confirmedEngineEntryCount = confirmedIdentities.Count
          activeCatalogEntryCount = activeEntries.Length
          corpusMatches = corpusMatches
          diagnostics = abiAuditDiagnostics }

    // ------------------------------------------------------------------
    // Versioned interface sprite renderer contracts
    // ------------------------------------------------------------------

    let mutable private rendererContractEntries: SpriteRendererContract list = []
    let mutable private rendererContractsLoadedFrom: string option = None

    let private parseStringArray (json: JsonValue) name =
        match json.TryGetProperty name with
        | Some(JsonValue.Array values) ->
            values
            |> Array.choose (function
                | JsonValue.String value when not (String.IsNullOrWhiteSpace value) -> Some value
                | _ -> None)
            |> Array.toList
        | _ -> []

    let private parseRendererContract (gameVersion: string option) (json: JsonValue) =
        match
            stringProperty json "renderer_subtype",
            stringProperty json "shader_file",
            parseStringArray json "effects"
        with
        | Some subtype, Some shaderFile, effects when not effects.IsEmpty ->
            let entryVersion = stringProperty json "game_version" |> Option.defaultValue "unknown"
            let stale =
                match gameVersion with
                | Some current -> not (entryVersion.Equals(current, StringComparison.OrdinalIgnoreCase))
                | None -> true

            Some
                { game = stringProperty json "game" |> Option.defaultValue "unknown"
                  gameVersion = entryVersion
                  rendererSubtype = subtype
                  shaderFile = shaderFile
                  effects = effects |> List.distinct
                  requiredInputs = parseStringArray json "required_inputs" |> List.distinct
                  evidence = stringProperty json "evidence" |> Option.defaultValue "official_vanilla_contract"
                  stale = stale
                  notes = stringProperty json "notes" }
        | _ -> None

    let loadSpriteRendererContractsFromText (gameVersion: string option) (source: string) (text: string) =
        try
            let json = JsonValue.Parse text
            let entries =
                match json.TryGetProperty "contracts" with
                | Some(JsonValue.Array values) -> values
                | _ -> [||]

            rendererContractEntries <- entries |> Array.choose (parseRendererContract gameVersion) |> Array.toList
            rendererContractsLoadedFrom <- Some source
        with ex ->
            rendererContractEntries <- []
            rendererContractsLoadedFrom <- None
            CWTools.Utilities.Utils.logWarning (
                sprintf "PdxShaderRuntime: failed to parse sprite renderer contracts %s: %s" source ex.Message
            )

    let loadSpriteRendererContracts (gameVersion: string option) (path: string) =
        if File.Exists path then
            try
                loadSpriteRendererContractsFromText gameVersion path (File.ReadAllText path)
            with ex ->
                rendererContractEntries <- []
                rendererContractsLoadedFrom <- None
                CWTools.Utilities.Utils.logWarning (
                    sprintf "PdxShaderRuntime: failed to read sprite renderer contracts %s: %s" path ex.Message
                )
        else
            rendererContractEntries <- []
            rendererContractsLoadedFrom <- None

    let resetSpriteRendererContracts () =
        rendererContractEntries <- []
        rendererContractsLoadedFrom <- None

    let activeSpriteRendererContracts () = rendererContractEntries |> List.filter (fun entry -> not entry.stale)
    let spriteRendererContractInfo () = rendererContractsLoadedFrom, rendererContractEntries

    // ------------------------------------------------------------------
    // Declaration extraction from the authoritative lossless syntax snapshot
    // ------------------------------------------------------------------

    let private declarationKindOfNode =
        function
        | PdxShaderSyntax.ShaderNodeKind.Effect -> Some EffectDeclaration
        | PdxShaderSyntax.ShaderNodeKind.VertexStruct -> Some VertexStructDeclaration
        | PdxShaderSyntax.ShaderNodeKind.ConstantBuffer -> Some ConstantBufferDeclaration
        | PdxShaderSyntax.ShaderNodeKind.Sampler -> Some SamplerDeclaration
        | PdxShaderSyntax.ShaderNodeKind.BlendState -> Some BlendStateDeclaration
        | PdxShaderSyntax.ShaderNodeKind.DepthStencilState -> Some DepthStencilStateDeclaration
        | PdxShaderSyntax.ShaderNodeKind.RasterizerState -> Some RasterizerStateDeclaration
        | _ -> None

    let declarationsFromSnapshot (snapshot: PdxShaderProject.ShaderSnapshot) : ShaderDeclaration list =
        let parsed = PdxShaderProject.semanticSnapshot snapshot

        let makeDeclaration
            (kind: ShaderDeclarationKind)
            (node: PdxShaderSyntax.ShaderSyntaxNode)
            (name: string)
            (nameSpan: PdxShaderSyntax.TextSpan)
            =
            let condition = PdxShaderPreprocessor.conditionAt nameSpan.startOffset parsed.preprocessor

            { stableId = sprintf "%s:%A:%s:%d" snapshot.canonicalPath kind name nameSpan.startOffset
              name = name
              kind = kind
              file = snapshot.displayPath
              logicalPath = snapshot.logicalPath
              origin = snapshot.origin
              range = offsetRange snapshot.displayPath snapshot.text node.span.startOffset node.span.Length
              selectionRange = offsetRange snapshot.displayPath snapshot.text nameSpan.startOffset nameSpan.Length
              presenceCondition = sprintf "%A" condition
              detail = None }

        let rec collect (mainCodeKind: ShaderDeclarationKind option) (node: PdxShaderSyntax.ShaderSyntaxNode) =
            [ match declarationKindOfNode node.kind, node.name, node.nameSpan with
              | Some kind, Some name, Some nameSpan -> yield makeDeclaration kind node name nameSpan
              | _ -> ()

              let childStage =
                  match node.kind with
                  | PdxShaderSyntax.ShaderNodeKind.VertexShader -> Some VertexMainCodeDeclaration
                  | PdxShaderSyntax.ShaderNodeKind.PixelShader -> Some PixelMainCodeDeclaration
                  | PdxShaderSyntax.ShaderNodeKind.GeometryShader -> Some GeometryMainCodeDeclaration
                  | _ -> mainCodeKind

              match node.kind, node.name, node.nameSpan, mainCodeKind with
              | PdxShaderSyntax.ShaderNodeKind.MainCode, Some name, Some nameSpan, Some kind ->
                  yield makeDeclaration kind node name nameSpan
              | _ -> ()

              for child in node.children do
                  yield! collect childStage child ]

        let syntaxDeclarations = collect None parsed.syntax.root

        let hlslDeclarations =
            parsed.hlsl.symbols
            |> List.choose (fun symbol ->
                let kind =
                    match symbol.kind with
                    | PdxShaderHlsl.StructSymbol -> Some HlslTypeDeclaration
                    | PdxShaderHlsl.FunctionSymbol -> Some HlslFunctionDeclaration
                    | PdxShaderHlsl.FieldSymbol
                    | PdxShaderHlsl.ParameterSymbol
                    | PdxShaderHlsl.GlobalVariableSymbol
                    | PdxShaderHlsl.LocalVariableSymbol -> Some HlslVariableDeclaration
                    | PdxShaderHlsl.ResourceSymbol -> Some ShaderResourceDeclaration
                    | PdxShaderHlsl.SamplerSymbol -> Some SamplerDeclaration
                    | PdxShaderHlsl.ConstantBufferSymbol -> Some ConstantBufferDeclaration
                    | _ -> None

                kind
                |> Option.map (fun kind ->
                    { stableId = symbol.id
                      name = symbol.name
                      kind = kind
                      file = snapshot.displayPath
                      logicalPath = snapshot.logicalPath
                      origin = snapshot.origin
                      range = offsetRange snapshot.displayPath snapshot.text symbol.span.startOffset symbol.span.Length
                      selectionRange = offsetRange snapshot.displayPath snapshot.text symbol.selectionSpan.startOffset symbol.selectionSpan.Length
                      presenceCondition = sprintf "%A" symbol.condition
                      detail = Some(sprintf "%A" symbol.symbolType) }))

        let macroDeclarations =
            parsed.preprocessor.macros
            |> List.map (fun macro ->
                let lineText = snapshot.text.Substring(macro.span.startOffset, macro.span.Length)
                let relative = lineText.IndexOf(macro.name, StringComparison.Ordinal)
                let selectionStart = macro.span.startOffset + max 0 relative

                { stableId = sprintf "%s:macro:%s:%d" snapshot.canonicalPath macro.name selectionStart
                  name = macro.name
                  kind = MacroDeclaration
                  file = snapshot.displayPath
                  logicalPath = snapshot.logicalPath
                  origin = snapshot.origin
                  range = offsetRange snapshot.displayPath snapshot.text macro.span.startOffset macro.span.Length
                  selectionRange = offsetRange snapshot.displayPath snapshot.text selectionStart macro.name.Length
                  presenceCondition = sprintf "%A" macro.condition
                  detail = Some(sprintf "%A" macro.kind) })

        syntaxDeclarations @ hlslDeclarations @ macroDeclarations
        |> List.distinctBy (fun declaration -> declaration.kind, declaration.selectionRange.StartLine, declaration.selectionRange.StartColumn, declaration.name)

    let semanticReferencesFromSnapshot (snapshot: PdxShaderProject.ShaderSnapshot) : ShaderSemanticReference list =
        let parsed = PdxShaderProject.semanticSnapshot snapshot

        let stageName =
            function
            | PdxShaderHlsl.VertexStage -> "vertex"
            | PdxShaderHlsl.PixelStage -> "pixel"
            | PdxShaderHlsl.GeometryStage -> "geometry"
            | PdxShaderHlsl.UnknownStage -> "unknown"

        let valueTokens (node: PdxShaderSyntax.ShaderSyntaxNode) =
            let tokens = parsed.syntax.tokens[node.tokenStart .. node.tokenEnd]
            let equalsIndex = tokens |> Array.tryFindIndex (fun token -> token.kind = PdxShaderSyntax.ShaderTokenKind.Equals)

            match equalsIndex with
            | None -> []
            | Some equalsIndex ->
                let mutable depth = 0

                [ for token in tokens[equalsIndex + 1 ..] do
                      match token.kind with
                      | PdxShaderSyntax.ShaderTokenKind.OpenBrace -> depth <- depth + 1
                      | PdxShaderSyntax.ShaderTokenKind.CloseBrace -> depth <- max 0 (depth - 1)
                      | PdxShaderSyntax.ShaderTokenKind.Identifier when depth <= 1 -> yield token
                      | PdxShaderSyntax.ShaderTokenKind.StringLiteral when depth <= 1 -> yield token
                      | _ -> () ]

        let outer = ResizeArray<ShaderSemanticReference>()

        let addOuter owner kind (token: PdxShaderSyntax.ShaderToken) =
            let quoted = token.kind = PdxShaderSyntax.ShaderTokenKind.StringLiteral && token.text.Length >= 2
            let target = if quoted then token.text.Substring(1, token.text.Length - 2) else token.text
            let startOffset = token.span.startOffset + (if quoted then 1 else 0)
            let length = max 1 (token.span.Length - (if quoted then 2 else 0))
            let condition = PdxShaderPreprocessor.conditionAt startOffset parsed.preprocessor

            outer.Add
                { sourceId = None
                  sourceName = owner
                  targetName = target
                  targetIds = []
                  kind = kind
                  file = snapshot.displayPath
                  logicalPath = snapshot.logicalPath
                  origin = snapshot.origin
                  span = offsetRange snapshot.displayPath snapshot.text startOffset length
                  presenceCondition = sprintf "%A" condition
                  stage = "unknown" }

        let rec collect owner (node: PdxShaderSyntax.ShaderSyntaxNode) =
            let owner =
                match node.kind, node.name with
                | PdxShaderSyntax.ShaderNodeKind.Effect, Some name -> Some name
                | PdxShaderSyntax.ShaderNodeKind.MainCode, Some name -> Some name
                | _ -> owner

            match node.kind, node.name with
            | PdxShaderSyntax.ShaderNodeKind.Property, Some property ->
                let referenceKind =
                    match property.ToLowerInvariant() with
                    | "vertexshader" -> Some EffectUsesVertexMainCode
                    | "pixelshader" -> Some EffectUsesPixelMainCode
                    | "geometryshader" -> Some EffectUsesGeometryMainCode
                    | "blendstate"
                    | "depthstencilstate"
                    | "rasterizerstate" -> Some EffectUsesRenderState
                    | "constantbuffers" -> Some MainCodeUsesConstantBuffer
                    | _ -> None

                referenceKind |> Option.iter (fun kind -> valueTokens node |> List.iter (addOuter owner kind))
            | _ -> ()

            node.children |> List.iter (collect owner)

        collect None parsed.syntax.root

        let hlsl =
            parsed.hlsl.references
            |> List.map (fun reference ->
                let kind =
                    match reference.kind with
                    | PdxShaderHlsl.CallReference -> HlslCallsFunction
                    | PdxShaderHlsl.TypeReference -> HlslUsesType
                    | PdxShaderHlsl.MemberReference -> HlslUsesMember
                    | _ -> HlslUsesSymbol
                let caller =
                    parsed.hlsl.calls
                    |> List.tryFind (fun call -> call.span = reference.span)
                    |> Option.bind _.callerId

                { sourceId = caller
                  sourceName = None
                  targetName = reference.name
                  targetIds = reference.candidateIds
                  kind = kind
                  file = snapshot.displayPath
                  logicalPath = snapshot.logicalPath
                  origin = snapshot.origin
                  span = offsetRange snapshot.displayPath snapshot.text reference.span.startOffset reference.span.Length
                  presenceCondition = sprintf "%A" reference.condition
                  stage = stageName reference.stage })

        (outer |> Seq.toList) @ hlsl

    // Bounded declaration cache also keys logical path/origin because declaration
    // provenance must refresh when resource metadata changes without a text edit.
    let private declarationCacheCap = 512
    let private declarationCache = Dictionary<string * string * string * PdxShaderProject.ShaderOrigin, ShaderDeclaration list>()
    let private declarationCacheLock = obj ()

    let private declarationsFromSnapshotCached (snapshot: PdxShaderProject.ShaderSnapshot) =
        let key =
            snapshot.canonicalPath,
            snapshot.contentHash,
            PdxShaderProject.normalizeLogicalPath snapshot.logicalPath,
            snapshot.origin

        lock declarationCacheLock (fun () ->
            match declarationCache.TryGetValue key with
            | true, declarations -> declarations
            | _ ->
                let declarations = declarationsFromSnapshot snapshot
                if declarationCache.Count >= declarationCacheCap then declarationCache.Clear()
                declarationCache[key] <- declarations
                declarations)

    // ------------------------------------------------------------------
    // Resource collection (mirrors PdxShaderFeatures.collectSnapshots)
    // ------------------------------------------------------------------

    /// Shader snapshots from resources, open documents (unsaved text wins) and the
    /// cached vanilla FX sources. A content-bearing resource always wins over a
    /// disk read of the same file; failed reads are logged and skipped.
    let collectShaderSnapshots (resources: Resource seq) (openDocuments: (string * string) list) : PdxShaderProject.ShaderSnapshot list =
        let materialized = Seq.toList resources

        let openByCanonical =
            openDocuments
            |> List.map (fun (path, text) -> PdxShaderProject.canonicalizePath path, (path, text))
            |> Map.ofList

        let openPaths = openByCanonical |> Map.toSeq |> Seq.map fst |> Set.ofSeq

        let contentSnapshots =
            materialized
            |> List.choose (function
                | FileWithContentResource(_, resource) when
                    resource.overwrite <> Overwrite.Overwritten
                    && PdxShaderProject.isShaderFile resource.filepath
                    && not (Set.contains (PdxShaderProject.canonicalizePath resource.filepath) openPaths)
                    ->
                    Some(
                        PdxShaderProject.createSnapshot
                            (PdxShaderProject.originForResource resource.scope resource.filepath)
                            resource.filepath
                            resource.logicalpath
                            resource.filetext
                    )
                | _ -> None)

        let contentPaths =
            contentSnapshots
            |> List.map (fun snapshot -> snapshot.canonicalPath)
            |> Set.ofList

        let diskSnapshot filepath logicalpath scope =
            let canonical = PdxShaderProject.canonicalizePath filepath

            if Set.contains canonical contentPaths || Set.contains canonical openPaths then
                None
            elif File.Exists filepath then
                try
                    Some(
                        PdxShaderProject.createSnapshot
                            (PdxShaderProject.originForResource scope filepath)
                            filepath
                            logicalpath
                            (File.ReadAllText filepath)
                    )
                with ex ->
                    CWTools.Utilities.Utils.logWarning (
                        sprintf "PdxShaderRuntime: failed to read shader file %s: %s" filepath ex.Message
                    )

                    None
            else
                None

        let fileSnapshots =
            materialized
            |> List.choose (function
                | FileResource(_, resource) when PdxShaderProject.isShaderFile resource.filepath ->
                    diskSnapshot resource.filepath resource.logicalpath resource.scope
                | EntityResource(_, resource) when PdxShaderProject.isShaderFile resource.filepath ->
                    diskSnapshot resource.filepath resource.logicalpath resource.scope
                | _ -> None)

        let openSnapshots =
            openByCanonical
            |> Map.toList
            |> List.map (fun (_, (path, text)) ->
                PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument path path text)

        let vanillaSnapshots =
            vanillaShaderSources ()
            |> List.choose (fun source ->
                let canonical = PdxShaderProject.canonicalizePath source.filepath

                if Set.contains canonical openPaths || Set.contains canonical contentPaths then
                    None
                else
                    Some(
                        PdxShaderProject.createSnapshot
                            PdxShaderProject.Vanilla
                            source.filepath
                            source.logicalpath
                            source.text
                    ))

        // One snapshot per canonical path, best origin first.
        contentSnapshots @ fileSnapshots @ openSnapshots @ vanillaSnapshots
        |> List.sortBy PdxShaderProject.sortKey
        |> List.distinctBy (fun snapshot -> snapshot.canonicalPath)

    /// Collect a bounded class of script sources. Content resources and open
    /// documents win over disk reads; returns sources plus a skipped-file count.
    let private collectSourcesWhere predicate (resources: Resource seq) (openDocuments: (string * string) list) : ScriptSource list * int =
        let byCanonical = Dictionary<string, int * ScriptSource>()
        let failedCanonical = HashSet<string>(StringComparer.Ordinal)

        let add priority source =
            let key = PdxShaderProject.canonicalizePath source.filepath
            failedCanonical.Remove key |> ignore

            match byCanonical.TryGetValue key with
            | true, (existingPriority, _) when existingPriority > priority -> ()
            | _ -> byCanonical[key] <- (priority, source)

        let markFailed path =
            let key = PdxShaderProject.canonicalizePath path
            if not (byCanonical.ContainsKey key) then failedCanonical.Add key |> ignore

        for resource in resources do
            match resource with
            | EntityResource(_, entity) when predicate entity.filepath ->
                if File.Exists entity.filepath then
                    try
                        add 0
                            { filepath = entity.filepath
                              logicalpath = entity.logicalpath
                              scope = entity.scope
                              text = File.ReadAllText entity.filepath }
                    with ex ->
                        markFailed entity.filepath

                        CWTools.Utilities.Utils.logWarning (
                            sprintf "PdxShaderRuntime: failed to read script file %s: %s" entity.filepath ex.Message
                        )
                else
                    markFailed entity.filepath
            | FileResource(_, file) when predicate file.filepath ->
                if File.Exists file.filepath then
                    try
                        add 0
                            { filepath = file.filepath
                              logicalpath = file.logicalpath
                              scope = file.scope
                              text = File.ReadAllText file.filepath }
                    with ex ->
                        markFailed file.filepath

                        CWTools.Utilities.Utils.logWarning (
                            sprintf "PdxShaderRuntime: failed to read script file %s: %s" file.filepath ex.Message
                        )
                else
                    markFailed file.filepath
            | FileWithContentResource(_, content) when
                content.overwrite <> Overwrite.Overwritten
                && predicate content.filepath
                ->
                add 1
                    { filepath = content.filepath
                      logicalpath = content.logicalpath
                      scope = content.scope
                      text = content.filetext }
            | _ -> ()

        for (path, text) in openDocuments do
            if predicate path then
                add 2
                    { filepath = path
                      logicalpath = path
                      scope = "workspace"
                      text = text }

        byCanonical.Values |> Seq.map snd |> List.ofSeq, failedCanonical.Count

    /// Script (.gfx/.asset) sources for Effect caller evidence extraction.
    let collectScriptSources resources openDocuments =
        collectSourcesWhere isEvidenceScriptFile resources openDocuments

    /// `.gui` sources used only for static GFX sprite-use edges.
    let private collectGuiSources resources openDocuments =
        collectSourcesWhere isGuiScriptFile resources openDocuments

    // ------------------------------------------------------------------
    // Model build
    // ------------------------------------------------------------------

    let private normalizeValuePath (path: string) = PdxShaderProject.normalizeLogicalPath path

    let private catalogEntryMatchesDeclaration (entry: AbiCatalogEntry) (declaration: ShaderDeclaration) =
        entry.entryKind.Equals("effect", StringComparison.OrdinalIgnoreCase)
        && entry.name.Equals(declaration.name, StringComparison.OrdinalIgnoreCase)
        && (match entry.shaderFile with
            | None -> true
            | Some catalogPath ->
                let declaredPath = normalizeValuePath declaration.logicalPath
                let wantedPath = normalizeValuePath catalogPath
                declaredPath = wantedPath
                || declaredPath.EndsWith("/" + wantedPath, StringComparison.Ordinal))

    /// Map each effective (best-origin) shader file selected by an effectFile
    /// assignment to the selecting evidence.
    let private selectedFileEvidence (snapshots: PdxShaderProject.ShaderSnapshot list) (evidence: ShaderCallEvidence list) : Map<string, ShaderCallEvidence list> =
        evidence
        |> List.filter (fun item -> item.kind = EffectFileSelection)
        |> List.choose (fun item ->
            let wanted = normalizeValuePath item.value

            let exactMatches =
                snapshots
                |> List.filter (fun snapshot ->
                    let logical = normalizeValuePath snapshot.logicalPath
                    logical = wanted)

            let matches =
                if not exactMatches.IsEmpty then
                    exactMatches
                else
                    let suffixMatches =
                        snapshots
                        |> List.filter (fun snapshot ->
                            let logical = normalizeValuePath snapshot.logicalPath
                            logical.EndsWith("/" + wanted, StringComparison.Ordinal))

                    let distinctLogicalPaths =
                        suffixMatches
                        |> List.map (fun snapshot -> normalizeValuePath snapshot.logicalPath)
                        |> List.distinct

                    // A basename/suffix that resolves to more than one logical path
                    // is ambiguous. Do not fabricate reachability by picking the
                    // first filesystem entry; the caller keeps the selection unresolved
                    // and the preflight/query layer reports the missing evidence.
                    if distinctLogicalPaths.Length = 1 then suffixMatches else []

            match matches |> List.sortBy PdxShaderProject.sortKey with
            | best :: _ -> Some(best.canonicalPath, item)
            | [] -> None)
        |> List.groupBy fst
        |> List.map (fun (path, pairs) -> path, pairs |> List.map snd)
        |> Map.ofList

    let resolveSemanticReferences
        (snapshots: PdxShaderProject.ShaderSnapshot list)
        (declarations: ShaderDeclaration list)
        (rawReferences: ShaderSemanticReference list)
        =
        let compileUnitPaths =
            snapshots
            |> List.map (fun snapshot ->
                snapshot.canonicalPath,
                (PdxShaderProject.buildCompileUnit snapshots snapshot).effective
                |> List.map _.canonicalPath
                |> Set.ofList)
            |> Map.ofList
        rawReferences
        |> List.map (fun reference ->
            let sourceCanonical = PdxShaderProject.canonicalizePath reference.file
            let visiblePaths = compileUnitPaths |> Map.tryFind sourceCanonical |> Option.defaultValue (Set.singleton sourceCanonical)
            let targetKinds =
                match reference.kind with
                | EffectUsesVertexMainCode -> [ VertexMainCodeDeclaration ]
                | EffectUsesPixelMainCode -> [ PixelMainCodeDeclaration ]
                | EffectUsesGeometryMainCode -> [ GeometryMainCodeDeclaration ]
                | EffectUsesRenderState -> [ BlendStateDeclaration; DepthStencilStateDeclaration; RasterizerStateDeclaration ]
                | MainCodeUsesConstantBuffer -> [ ConstantBufferDeclaration ]
                | HlslCallsFunction -> [ HlslFunctionDeclaration ]
                | HlslUsesType -> [ HlslTypeDeclaration; VertexStructDeclaration ]
                | HlslUsesMember
                | HlslUsesSymbol -> [ HlslVariableDeclaration; ShaderResourceDeclaration; SamplerDeclaration ]
            let resolvedIds =
                if not reference.targetIds.IsEmpty then reference.targetIds
                else
                    declarations
                    |> List.filter (fun declaration ->
                        targetKinds |> List.contains declaration.kind
                        && declaration.name.Equals(reference.targetName, StringComparison.OrdinalIgnoreCase)
                        && visiblePaths.Contains(PdxShaderProject.canonicalizePath declaration.file))
                    |> List.map _.stableId
            let sourceId =
                reference.sourceId
                |> Option.orElseWith (fun () ->
                    reference.sourceName
                    |> Option.bind (fun sourceName ->
                        declarations
                        |> List.tryFind (fun declaration ->
                            declaration.name.Equals(sourceName, StringComparison.OrdinalIgnoreCase)
                            && PdxShaderProject.sameFilePath declaration.file reference.file)
                        |> Option.map _.stableId))
            { reference with
                sourceId = sourceId
                targetIds = resolvedIds |> List.distinct |> List.sort })

    /// Build the immutable runtime model from game resources and open documents.
    /// gameVersion is only provenance metadata; pass None when unknown.
    let buildModel (gameVersion: string option) (resources: Resource seq) (openDocuments: (string * string) list) : ShaderRuntimeModel =
        let materialized = Seq.cache resources
        let shaderDocs, scriptDocs = openDocuments |> List.partition (fun (path, _) -> PdxShaderProject.isShaderFile path)
        let snapshots = collectShaderSnapshots materialized shaderDocs
        let scriptSources, skipped = collectScriptSources materialized scriptDocs
        let guiSources, _ = collectGuiSources materialized scriptDocs
        let declarations = snapshots |> List.collect declarationsFromSnapshotCached
        let rawSemanticReferences = snapshots |> List.collect semanticReferencesFromSnapshot
        let semanticReferences = resolveSemanticReferences snapshots declarations rawSemanticReferences
        let evidence = scriptSources |> List.collect extractEvidenceCached
        let interfaceSprites =
            scriptSources
            |> List.filter (fun source -> Path.GetExtension(source.filepath).Equals(".gfx", StringComparison.OrdinalIgnoreCase))
            |> List.collect (fun source ->
                extractInterfaceSpriteInvocationsCached
                    (PdxShaderProject.originForResource source.scope source.filepath)
                    source.filepath
                    source.logicalpath
                    source.text)
        let guiSpriteUses =
            guiSources
            |> List.collect (fun source ->
                extractGuiSpriteUsesCached
                    (PdxShaderProject.originForResource source.scope source.filepath)
                    source.filepath
                    source.logicalpath
                    source.text)
        let catalog = activeCatalog ()
        let rendererContracts = activeSpriteRendererContracts ()
        let staleCatalogCount = catalogEntries.Length - catalog.Length
        let selectedFiles = selectedFileEvidence snapshots evidence

        let effects =
            declarations
            |> List.filter (fun declaration -> declaration.kind = EffectDeclaration)
            |> List.map (fun declaration ->
                let nameEvidence =
                    evidence
                    |> List.filter (fun item ->
                        item.kind = ShaderAssignment
                        && item.value.Equals(declaration.name, StringComparison.OrdinalIgnoreCase))

                let fileEvidence =
                    selectedFiles
                    |> Map.tryFind (PdxShaderProject.canonicalizePath declaration.file)
                    |> Option.defaultValue []

                let contractEvidence =
                    fileEvidence
                    |> List.filter (fun evidence ->
                        match evidence.rendererSubtype with
                        | None -> false
                        | Some subtype ->
                            rendererContracts
                            |> List.exists (fun contract ->
                                contract.rendererSubtype.Equals(subtype, StringComparison.OrdinalIgnoreCase)
                                && normalizeValuePath contract.shaderFile = normalizeValuePath declaration.logicalPath
                                && normalizeValuePath evidence.value = normalizeValuePath contract.shaderFile
                                && contract.effects
                                   |> List.exists (fun effect -> effect.Equals(declaration.name, StringComparison.OrdinalIgnoreCase))))

                let all = nameEvidence @ fileEvidence

                let catalogEntry =
                    catalog
                    |> List.tryFind (fun entry -> catalogEntryMatchesDeclaration entry declaration)

                let reachability =
                    if not nameEvidence.IsEmpty then
                        DataExplicit all
                    elif not contractEvidence.IsEmpty then
                        EffectFileConvention contractEvidence
                    elif not fileEvidence.IsEmpty then
                        EffectFileConventionCandidate all
                    else
                        match catalogEntry with
                        | Some entry -> EngineHardcoded entry
                        | None -> EngineOrUnreferenced

                { declaration = declaration
                  reachability = reachability
                  allEvidence = all })

        { gameVersion = gameVersion |> Option.defaultValue "unknown"
          snapshots = snapshots
          declarations = declarations
          semanticReferences = semanticReferences
          effects = effects
          evidence = evidence
          interfaceSprites = interfaceSprites
          guiSpriteUses = guiSpriteUses
          rendererContracts = rendererContracts
          catalog = catalog
          staleCatalogCount = staleCatalogCount
          scriptFilesScanned = scriptSources.Length
          scriptFilesSkipped = skipped }

    let rendererContractForInvocation (model: ShaderRuntimeModel) (invocation: InterfaceSpriteInvocation) =
        model.rendererContracts
        |> List.tryFind (fun contract ->
            contract.rendererSubtype.Equals(invocation.rendererSubtype, StringComparison.OrdinalIgnoreCase)
            && normalizeValuePath contract.shaderFile = normalizeValuePath invocation.shaderFile)

    /// Empty means the target renderer contract, required inputs and exact Effect
    /// declarations are all available for the active game version.
    let validateRendererInvocation (model: ShaderRuntimeModel) (invocation: InterfaceSpriteInvocation) : string list =
        match rendererContractForInvocation model invocation with
        | None ->
            [ sprintf
                  "no version-matched renderer contract for subtype '%s' and shader '%s'"
                  invocation.rendererSubtype
                  invocation.shaderFile ]
        | Some contract ->
            let inputNames =
                invocation.resourceInputs
                |> List.map (fun input -> input.field.ToLowerInvariant())
                |> Set.ofList

            let missingInputs =
                contract.requiredInputs
                |> List.filter (fun required -> not (inputNames.Contains(required.ToLowerInvariant())))
                |> List.map (fun required -> sprintf "renderer contract requires input '%s'" required)

            let declaredEffects =
                model.declarations
                |> List.filter (fun declaration ->
                    declaration.kind = EffectDeclaration
                    && normalizeValuePath declaration.logicalPath = normalizeValuePath contract.shaderFile)
                |> List.map _.name

            let missingEffects =
                contract.effects
                |> List.filter (fun required ->
                    declaredEffects
                    |> List.exists (fun declared -> declared.Equals(required, StringComparison.OrdinalIgnoreCase))
                    |> not)
                |> List.map (fun required -> sprintf "renderer contract requires Effect '%s'" required)

            missingInputs @ missingEffects

    /// Compile unit for an arbitrary shader file, plus the snapshot list used to
    /// build it (for reverse-dependency lookups). Open documents win over disk text.
    let compileUnitFor (resources: Resource seq) (openDocuments: (string * string) list) (filepath: string) : (PdxShaderProject.CompileUnit * PdxShaderProject.ShaderSnapshot list) option =
        let snapshots =
            collectShaderSnapshots resources (openDocuments |> List.filter (fun (path, _) -> PdxShaderProject.isShaderFile path))

        let canonical = PdxShaderProject.canonicalizePath filepath

        snapshots
        |> List.filter (fun snapshot -> snapshot.canonicalPath = canonical)
        |> List.sortBy PdxShaderProject.sortKey
        |> List.tryHead
        |> Option.map (fun root -> PdxShaderProject.buildCompileUnit snapshots root, snapshots)

    /// Transitive reverse dependencies: display paths of every snapshot that can
    /// reach the given file through Includes, stable sorted, excluding the file itself.
    let reverseIncluders (snapshots: PdxShaderProject.ShaderSnapshot list) (filepath: string) : string list =
        let reverse = PdxShaderProject.reverseIncludeMap snapshots
        let target = PdxShaderProject.canonicalizePath filepath
        let visited = HashSet<string>(StringComparer.Ordinal)
        let queue = Queue<string>()
        visited.Add target |> ignore
        queue.Enqueue target

        while queue.Count > 0 do
            let current = queue.Dequeue()

            match reverse |> Map.tryFind current with
            | Some parents ->
                for parent in parents do
                    if visited.Add parent then queue.Enqueue parent
            | None -> ()

        let displayByCanonical =
            snapshots
            |> List.sortBy PdxShaderProject.sortKey
            |> List.distinctBy (fun snapshot -> snapshot.canonicalPath)
            |> List.map (fun snapshot -> snapshot.canonicalPath, snapshot.displayPath)
            |> Map.ofList

        visited
        |> Seq.filter (fun path -> path <> target)
        |> Seq.choose (fun path -> displayByCanonical |> Map.tryFind path)
        |> Seq.sort
        |> Seq.toList

    // ------------------------------------------------------------------
    // Query API (pure over the collected model)
    // ------------------------------------------------------------------

    let private reachabilityRank =
        function
        | DataExplicit _ -> 0
        | EffectFileConvention _ -> 1
        | EffectFileConventionCandidate _ -> 2
        | EngineHardcoded _ -> 3
        | EngineOrUnreferenced -> 4

    type EffectReachabilityResult =
        { name: string
          reachability: EffectReachability
          declarations: ShaderDeclaration list
          evidence: ShaderCallEvidence list
          gameVersion: string }

    /// Highest-certainty classification across all declarations of the Effect,
    /// with the union of every declaration's evidence.
    let effectReachability (model: ShaderRuntimeModel) (effectName: string) : EffectReachabilityResult option =
        let infos =
            model.effects
            |> List.filter (fun info -> info.declaration.name.Equals(effectName, StringComparison.OrdinalIgnoreCase))

        if infos.IsEmpty then
            None
        else
            let best = infos |> List.minBy (fun info -> reachabilityRank info.reachability)

            let evidence =
                infos
                |> List.collect (fun info -> info.allEvidence)
                |> List.distinctBy (fun item -> item.kind, item.sourceFile, item.span)

            { name = best.declaration.name
              reachability = best.reachability
              declarations =
                infos
                |> List.map (fun info -> info.declaration)
                |> List.sortBy (fun declaration -> PdxShaderProject.originRank declaration.origin, declaration.file)
              evidence = evidence
              gameVersion = model.gameVersion }
            |> Some

    /// All evidence associated with the named Effect. This includes direct
    /// `shader = effectName` callers and `effectFile` selections of files that
    /// declare the Effect; the latter remains convention-candidate evidence until
    /// a renderer contract confirms the concrete entry.
    let callersOf (model: ShaderRuntimeModel) (effectName: string) : ShaderCallEvidence list =
        let direct =
            model.evidence
            |> List.filter (fun item ->
                item.kind = ShaderAssignment
                && item.value.Equals(effectName, StringComparison.OrdinalIgnoreCase))

        let declarationEvidence =
            model.effects
            |> List.filter (fun info -> info.declaration.name.Equals(effectName, StringComparison.OrdinalIgnoreCase))
            |> List.collect (fun info -> info.allEvidence)

        direct @ declarationEvidence
        |> List.distinctBy (fun item -> item.kind, item.sourceFile, item.span)
        |> List.sortBy (fun item -> item.sourceFile, item.span.StartLine, item.span.StartColumn)

    /// Every declared Effect with its classification, stable sorted.
    let allEffects (model: ShaderRuntimeModel) : (ShaderDeclaration * EffectReachability) list =
        model.effects
        |> List.map (fun info -> info.declaration, info.reachability)
        |> List.sortBy (fun (declaration, _) ->
            declaration.name.ToLowerInvariant(), PdxShaderProject.originRank declaration.origin, declaration.file)

    /// Review queue for ABI discovery. These are candidates only: this report never
    /// upgrades an Effect to engine_hardcoded and explicitly preserves uncertainty.
    let abiCandidateReport (model: ShaderRuntimeModel) : AbiCandidate list =
        allEffects model
        |> List.choose (fun (declaration, reachability) ->
            match reachability with
            | EffectFileConventionCandidate _ ->
                Some
                    { name = declaration.name
                      shaderFile = declaration.logicalPath
                      classification = "effect_file_convention_candidate"
                      reviewReason = "A renderer selects the file, but no reviewed renderer/EXE contract proves this concrete Effect entry." }
            | EngineOrUnreferenced ->
                Some
                    { name = declaration.name
                      shaderFile = declaration.logicalPath
                      classification = "engine_or_unreferenced"
                      reviewReason = "No textual or reviewed ABI evidence is known; absence of a text caller is not proof of an EXE call." }
            | _ -> None)
        |> List.distinctBy (fun candidate -> candidate.name.ToLowerInvariant(), PdxShaderProject.normalizeLogicalPath candidate.shaderFile)
        |> List.sortBy (fun candidate -> candidate.name.ToLowerInvariant(), candidate.shaderFile)

    type VanillaComparison =
        { name: string
          effective: ShaderDeclaration list
          overriddenVanilla: ShaderDeclaration list }

    /// Effective (best origin rank) declarations versus the vanilla declarations
    /// they override. Effects only; an unknown name yields empty lists.
    let compareWithVanilla (model: ShaderRuntimeModel) (effectName: string) : VanillaComparison =
        let declarations =
            model.declarations
            |> List.filter (fun declaration ->
                declaration.kind = EffectDeclaration
                && declaration.name.Equals(effectName, StringComparison.OrdinalIgnoreCase))
            |> List.sortBy (fun declaration -> PdxShaderProject.originRank declaration.origin, declaration.file)

        let byLogicalPath =
            declarations
            |> List.groupBy (fun declaration -> PdxShaderProject.normalizeLogicalPath declaration.logicalPath)

        let effective, overridden =
            byLogicalPath
            |> List.map (fun (_, sameLogicalFile) ->
                let bestRank =
                    sameLogicalFile
                    |> List.map (fun declaration -> PdxShaderProject.originRank declaration.origin)
                    |> List.min

                sameLogicalFile
                |> List.filter (fun declaration -> PdxShaderProject.originRank declaration.origin = bestRank),
                sameLogicalFile
                |> List.filter (fun declaration ->
                    declaration.origin = PdxShaderProject.Vanilla
                    && PdxShaderProject.originRank declaration.origin > bestRank))
            |> List.unzip

        { name = effectName
          effective = effective |> List.concat
          overriddenVanilla = overridden |> List.concat }

    /// Safe-rename decision for a classification (plan section 8.5).
    let renamePolicyForReachability (reachability: EffectReachability) : RenamePolicyDecision =
        match reachability with
        | DataExplicit evidence when evidence |> List.exists (fun item -> item.kind = EffectFileSelection) ->
            RenameDenied(
                "data_explicit effect also has effectFile selection evidence; located data callers do not eliminate the renderer-convention ABI risk"
            )
        | DataExplicit evidence ->
            RenameAllowed(
                sprintf
                    "data_explicit effect with %d locatable caller(s); rename may be previewed as a workspace edit"
                    evidence.Length
            )
        | EffectFileConvention _ ->
            RenameDenied(
                "effect_file_convention effect: the renderer selects this entry by contract; renaming breaks the convention"
            )
        | EffectFileConventionCandidate _ ->
            RenameDenied(
                "effect_file_convention_candidate effect: the declaring file is selected via effectFile and the renderer may choose this entry by name; convention risk cannot be excluded until renderer-contract profiles exist"
            )
        | EngineHardcoded entry ->
            match entry.renamePolicy with
            | CatalogAllowed ->
                RenameAllowed(
                    sprintf "engine_hardcoded effect whose ABI catalog entry (game %s) explicitly allows rename" entry.gameVersion
                )
            | CatalogForbidden ->
                RenameDenied(
                    sprintf "engine_hardcoded effect: curated ABI catalog entry (game %s) forbids rename" entry.gameVersion
                )
        | EngineOrUnreferenced ->
            RenameRequiresExplicitForce(
                "engine_or_unreferenced effect: no textual caller and no catalog entry, so engine use can neither be proven nor disproven; rename requires explicit user force"
            )

    /// Safe-rename decision for a named Effect. Undeclared names are denied:
    /// there is no declaration to rename.
    let renamePolicy (model: ShaderRuntimeModel) (effectName: string) : RenamePolicyDecision =
        match effectReachability model effectName with
        | Some result when
            model.catalog
            |> List.exists (fun entry ->
                entry.renamePolicy = CatalogForbidden
                && result.declarations |> List.exists (catalogEntryMatchesDeclaration entry))
            ->
            RenameDenied(
                sprintf
                    "Effect \"%s\" has an active version-matched ABI catalog entry that forbids rename, regardless of additional textual callers"
                    effectName
            )
        | Some result when result.declarations.Length > 1 ->
            RenameRequiresExplicitForce(
                sprintf
                    "Effect name \"%s\" has %d declarations across known shader files; a name-only rename cannot prove which ABI/contracts share the name"
                    effectName
                    result.declarations.Length
            )
        | Some result when model.scriptFilesSkipped > 0 ->
            RenameRequiresExplicitForce(
                sprintf
                    "shader caller evidence is incomplete because %d .gfx/.asset file(s) could not be read"
                    model.scriptFilesSkipped
            )
        | Some result -> renamePolicyForReachability result.reachability
        | None -> RenameDenied(sprintf "\"%s\" is not a declared Effect in the known shader files" effectName)

    /// Provenance descriptors for API consumers (confidence vocabulary of the plan).
    let reachabilityConfidence =
        function
        | DataExplicit _ -> "explicit"
        | EffectFileConvention _
        | EffectFileConventionCandidate _ -> "derived"
        | EngineHardcoded _ -> "curated"
        | EngineOrUnreferenced -> "unknown"

    let evidenceSourceKind (evidence: ShaderCallEvidence) =
        match evidence.kind with
        | EffectFileSelection -> "effectFile"
        | ShaderAssignment ->
            if evidence.sourceFile.EndsWith(".asset", StringComparison.OrdinalIgnoreCase) then
                "asset"
            else
                "gfx"

    let evidenceConfidence (evidence: ShaderCallEvidence) =
        match evidence.kind with
        | ShaderAssignment -> "explicit"
        | EffectFileSelection -> "derived"
