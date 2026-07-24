namespace CWTools.Games

open CWTools.Utilities.Position
open CWTools.Common
open CWTools.Process.Scopes

type SymbolLocalisationInfo = { key: string; value: string }

type SymbolInformation =
    { typename: string
      name: string
      localisation: SymbolLocalisationInfo list
      ruleDescription: string option
      ruleRequiredScopes: string list }

type GraphDataItem =
    {
        id: string
        displayName: string option
        documentation: string option
        /// name * isOutgoing
        references: (string * bool * string option) list
        location: range option
        details: Map<string, string list> option
        /// Whether this item is in the files given (as opposed to only referenced to)
        isPrimary: bool
        entityType: string
        entityTypeDisplayName: string option
        abbreviation: string option
    }

type GraphDataRequest = string list -> string -> int -> GraphDataItem list



type CWRelatedError = { location: range; message: string }

type CWError =
    { code: string
      severity: Severity
      range: range
      keyLength: int
      message: string
      data: string option
      relatedErrors: CWRelatedError list option }

type CachedRuleMetadata =
    { typeDefs: Map<string, array<TypeDefInfo>>
      enumDefs: Map<string, string * array<string>>
      varDefs: Map<string, array<string * range>>
      loc: (Lang * Set<string>) array
      files: Set<string>
      scriptedLoc: string array }

type CompletionCategory =
    | Link = 1uy
    | Global = 2uy
    | Variable = 3uy
    | Value = 4uy
    | Other = 5uy

type CompletionResponse =
    | Simple of label: string * score: int option * CompletionCategory
    | Detailed of label: string * desc: string option * score: int option * CompletionCategory
    | Snippet of label: string * snippet: string * desc: string option * score: int option * CompletionCategory

    static member CreateSimple(label: string) = Simple(label, None, CompletionCategory.Other)

    static member CreateSnippet(label, snippet, desc) =
        Snippet(label, snippet, desc, None, CompletionCategory.Other)

type InteractiveFileKind =
    | EntityFile
    | LocalisationFile
    | ShaderFile

/// Prepared editor update. The resource is parsed but has not yet been committed
/// to the live game state, so callers may build it without taking the write lock.
type StagedFileUpdate =
    { filepath: string
      fileText: string
      kind: InteractiveFileKind
      resourceUpdate: PreparedResourceUpdate }

type StagedScriptedTypes =
    { typeDefInfo: Map<string, TypeDefInfo array>
      tempTypeMap: Map<string, CWTools.Utilities.Utils2.PrefixOptimisedStringSet>
      typeDefInfoForValidation: Map<string, struct (string * range) array>
      /// lookup.typeDefInfo reference the fold was seeded from; commit-time ReferenceEquals guard
      baseTypeDefInfo: Map<string, TypeDefInfo array>
      /// Dynamic enum state used by scripted parameters is staged with the type index.
      baseEnumDefs: obj
      newEnumDefs: obj
      newTempEnumMap: obj
      ruleService: obj
      infoService: obj
      completionService: obj }

type StagedTypeIndex =
    { typeDefInfo: Map<string, TypeDefInfo array>
      tempTypeMap: Map<string, CWTools.Utilities.Utils2.PrefixOptimisedStringSet>
      typeDefInfoForValidation: Map<string, struct (string * range) array>
      /// True only when validation/completion-visible type metadata changed.
      /// Source ranges are deliberately excluded so body-only edits can update
      /// navigation positions without forcing a full rules/localisation rebuild.
      semanticChanged: bool
      /// lookup.typeDefInfo reference the fold was seeded from; commit-time ReferenceEquals guard
      baseTypeDefInfo: Map<string, TypeDefInfo array> }

/// Staged full rules refresh: the heavy rebuild runs against a temporary lookup clone
/// without holding the write lock. Prepare then releases the clone and retains only
/// its structurally-shared field snapshot for the brief write-locked commit.
type StagedCacheRefresh =
    { lookupSnapshot: LookupFieldSnapshot
      /// Commit-time ReferenceEquals guards: the live state must still match these
      baseTypeDefInfo: obj
      baseVarDefInfo: obj
      baseConfigRules: obj
      newTempTypeMap: obj
      newTempEnumMap: obj
      newRulesDataGenerated: bool
      ruleService: obj
      infoService: obj
      completionService: obj }

/// Incremental localisation dependency delta accumulated since the previous
/// deep analysis pass. Keys are language-agnostic because script references
/// and required type localisation apply to every configured language.
type LocalisationDelta =
    { changedKeys: string array
      affectedLocalisationFiles: string array
      semanticChanged: bool }

type IncrementalLocalisationResult =
    { affectedFiles: string array
      errors: CWError list }

/// Optional precise localisation invalidation. Games that do not implement it
/// keep the existing full localisation refresh behaviour.
type IIncrementalLocalisation =
    abstract TakeLocalisationDelta: unit -> LocalisationDelta option
    abstract ValidateLocalisationDelta: LocalisationDelta -> IncrementalLocalisationResult
    abstract ValidateLocalisationFiles: string array -> IncrementalLocalisationResult

type IIncrementalTypeIndex =
    abstract PrepareTypeIndex: string list -> StagedTypeIndex option
    abstract CommitTypeIndex: StagedTypeIndex -> bool
    abstract RemoveTypeIndex: string list -> bool

/// Optional semantic contribution fingerprint for a loaded entity. It covers
/// cross-file definitions that are not represented by TypeDefInfo (for example
/// value_set variables and saved event targets), allowing body-only edits to
/// remain local without hiding real global changes.
type ISemanticDeltaProvider =
    abstract SemanticSignatureForFile: string -> string array option

/// Optional cooperative cancellation for latency-sensitive editor validation.
/// Returning None means the caller's snapshot was superseded and no partial
/// diagnostics or validation-cache writes are safe to publish.
type ICancellableFileValidation =
    abstract ValidateFileInteractiveCancellable:
        StagedFileUpdate * (unit -> bool) -> CWError list option
    abstract ValidateFileCancellable:
        bool * string * (unit -> bool) -> CWError list option

type ScopeInferenceInfo =
    { kind: string
      candidates: string list
      resolvedScope: string
      certainty: string
      evidence: string list }

type IScopeInferenceProvider =
    abstract ScopeInferenceAtPos: pos -> string -> string -> ScopeContext -> ScopeInferenceInfo option

type IGame =
    abstract ParserErrors: unit -> (string * string * FParsec.Position) list
    abstract ValidationErrors: unit -> CWError list
    abstract LocalisationErrors: bool * bool -> CWError list
    abstract Folders: unit -> (string * string) array
    abstract AllFiles: unit -> Resource list
    abstract AllLoadedLocalisation: unit -> string list
    abstract UpdateFile: bool -> string -> string option -> CWError list
    /// Latency-sensitive editor update: refresh the resource and run only current-entity rule validation.
    abstract UpdateFileInteractive: string -> string option -> CWError list
    /// Parse an editor update without mutating the live game state.
    abstract PrepareUpdateFileInteractive: string -> string option -> StagedFileUpdate
    /// Atomically install a prepared editor resource. The caller holds the write lock.
    abstract CommitUpdateFileInteractive: StagedFileUpdate -> bool
    /// Validate the committed editor resource without mutating validation caches.
    abstract ValidateFileInteractive: StagedFileUpdate -> CWError list
    abstract ValidateFile: bool -> string -> CWError list
    /// Deep-validate several files in one validation round so shared indexes are built once.
    abstract ValidateFiles: string list -> CWError list
    abstract Complete: pos -> string -> string -> CompletionResponse list
    abstract GoToType: pos -> string -> string -> range option
    abstract FindAllRefs: pos -> string -> string -> range list option
    abstract FindAllRefsByType: string -> string -> range list
    abstract TypeReferenceIndex: unit -> Map<string * string, range list>
    abstract ReplaceConfigRules: (string * string) list -> unit
    abstract RefreshCaches: unit -> unit
    /// Lockless build phase of a staged full cache refresh; None when not supported.
    abstract PrepareRefreshCaches: unit -> StagedCacheRefresh option
    /// Write-locked commit; false when a guard fails and a locked RefreshCaches is needed.
    abstract CommitRefreshCaches: StagedCacheRefresh -> bool
    abstract RefreshScriptedTypes: string list -> bool
    abstract RemoveScriptedTypes: string list -> bool
    /// Lockless build phase of an incremental scripted-type refresh; None when not applicable.
    abstract PrepareScriptedTypes: string list -> StagedScriptedTypes option
    /// Write-locked swap phase; false when a guard fails and a full refresh is needed.
    abstract CommitScriptedTypes: StagedScriptedTypes -> bool
    abstract RefreshLocalisationCaches: unit -> unit
    abstract CleanupCache: Set<string> -> unit
    abstract InvalidateFileCache: string -> unit
    abstract ForceRecompute: unit -> unit
    abstract ForceDynamicParameterData: int * int -> int
    abstract GetInlineScriptCallers: string -> string list
    abstract RefreshInlineScriptCallers: string list -> string list
    abstract Types: unit -> Map<string, TypeDefInfo array>
    abstract TypeDefs: unit -> CWTools.Rules.TypeDefinition list
    abstract InfoAtPos: pos -> string -> string -> SymbolInformation option
    abstract OverrideModeAtPath: string -> CWTools.Rules.ConfigPriority option
    abstract OverrideModes: unit -> CWTools.Rules.ConfigPriority array
    abstract OverrideModesInfo: unit -> CWTools.Rules.ConfigOverrideModeInfo array
    abstract GetPossibleCodeEdits: string -> string -> range list
    abstract GetCodeEdits: string -> string -> (range seq * pos * string) list option
    abstract GetEventGraphData: GraphDataRequest
    abstract ScriptedTriggers: unit -> Effect list
    abstract ScriptedEffects: unit -> Effect list
    abstract ScriptedVariables: unit -> (string * string) list
    abstract StaticModifiers: unit -> StaticModifier array
    abstract ScopesAtPos: pos -> string -> string -> ScopeContext option
    abstract GetEmbeddedMetadata: unit -> CachedRuleMetadata

type IGame<'T when 'T :> ComputedData> =
    inherit IGame
    abstract AllEntities: unit -> struct (Entity * Lazy<'T>) seq
    abstract References: unit -> References<'T>
