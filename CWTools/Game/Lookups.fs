namespace CWTools.Games

open CWTools.Common
open CWTools.Rules
open CWTools.Process.Scopes
open CWTools.Utilities.Position
open Files
open CWTools.Process.Localisation

/// Explicit source-field snapshot used by staged cache refreshes. Values remain
/// structurally shared with the refreshed lookup, while derived lazy indexes are
/// rebuilt when the snapshot is applied.
type private LookupBaseSnapshot =
    { allCoreLinks: Effect list
      onlyScriptedEffects: Effect list
      onlyScriptedTriggers: Effect list
      rootFolders: WorkspaceDirectoryInput array
      staticModifiers: StaticModifier array
      coreModifiers: ActualModifier array
      embeddedScriptedLoc: string array
      realScriptedLoc: string array
      proccessedLoc: (Lang * Collections.Map<string, LocEntry>) list
      technologies: (string * string list) list
      configRules: RootRule array
      typeDefs: TypeDefinition list
      enumDefs: Map<string, string * (string * range option) array>
      typeDefInfo: Map<string, TypeDefInfo array>
      typeDefInfoForValidation: Map<string, struct (string * range) array>
      varDefInfo: Map<string, (string * range) array>
      extendedConfigMetadata: ExtendedConfigMetadata
      savedEventTargets: ResizeArray<string * range * Scope>
      scriptedVariables: (string * string) list
      globalScriptedVariableNames: string list }

type private LookupSubtypeSnapshot =
    | LookupBase
    | LookupJomini of scriptedEffectKeys: string list
    | LookupCK2 of landedTitles: Collections.Map<TitleType * bool, string list> * provinces: string array
    | LookupEU4 of scriptedEffectKeys: string array * trueLegacyGovernments: string array
    | LookupHOI4 of provinces: string array
    | LookupSTL
    | LookupIR of scriptedEffectKeys: string list * provinces: string array * characters: string array
    | LookupVIC2 of provinces: string array

type LookupFieldSnapshot =
    private
        { baseFields: LookupBaseSnapshot
          subtype: LookupSubtypeSnapshot }

type Lookup() =

    let mutable _allCoreLinks: Effect list = []

    let getTriggers () =
        _allCoreLinks
        |> List.filter (fun l -> l.Type = EffectType.Trigger || l.Type = EffectType.ValueTrigger)

    let mutable _triggers: Lazy<Effect list> = lazy []
    let mutable _triggersMap: Lazy<EffectMap> = lazy (EffectMap())

    let resetTriggers () =
        _triggersMap <- lazy (getTriggers () |> EffectMap.FromList)
        _triggers <- lazy (getTriggers ())
    let getEffects () =
        _allCoreLinks |> List.filter (fun l -> l.Type = EffectType.Effect)

    let mutable _effects: Lazy<Effect list> = lazy []
    let mutable _effectsMap: Lazy<EffectMap> = lazy EffectMap()

    let resetEffects () =
        _effectsMap <- lazy (getEffects () |> (fun l -> EffectMap.FromList(l)))
        _effects <- lazy (getEffects ())
    let getEventTargetLinks () =
        _allCoreLinks |> List.filter (fun l -> l.Type = EffectType.Link)

    let mutable _eventTargetLinks: Lazy<Effect list> = lazy []
    let mutable _eventTargetLinksMap: Lazy<EffectMap> = lazy EffectMap()

    let resetEventTargetLinks () =
        _eventTargetLinksMap <- lazy (getEventTargetLinks () |> EffectMap.FromList)
        _eventTargetLinks <- lazy (getEventTargetLinks ())
    let getValueTriggers () =
        _allCoreLinks |> List.filter (fun l -> l.Type = EffectType.ValueTrigger)

    let mutable _valueTriggers: Lazy<Effect list> = lazy []
    let mutable _valueTriggersMap: Lazy<EffectMap> = lazy EffectMap()

    let resetValueTriggers () =
        _valueTriggersMap <- lazy (getValueTriggers () |> EffectMap.FromList)
        _valueTriggers <- lazy (getValueTriggers ())
    member _.allCoreLinks
        with get () = _allCoreLinks
        and set value =
            _allCoreLinks <- value
            resetTriggers ()
            resetEffects ()
            resetEventTargetLinks ()
            resetValueTriggers ()

    member _.triggers = _triggers.Force()
    member this.triggersMap = _triggersMap.Force()
    member _.effects = _effects.Force()
    member this.effectsMap = _effectsMap.Force()
    member _.eventTargetLinks = _eventTargetLinks.Force()
    member this.eventTargetLinksMap = _eventTargetLinksMap.Force()
    member _.valueTriggers = _valueTriggers.Force()
    member this.valueTriggerMap = _valueTriggersMap.Force()    member val onlyScriptedEffects: Effect list = [] with get, set
    member val onlyScriptedTriggers: Effect list = [] with get, set

    member val rootFolders: WorkspaceDirectoryInput array = [||] with get, set
    member val staticModifiers: StaticModifier array = [||] with get, set
    member val coreModifiers: ActualModifier array = [||] with get, set
    member val embeddedScriptedLoc: string array = [||] with get, set
    member val _realScriptedLoc: string array = [||] with get, set
    member this.scriptedLoc = Array.append this.embeddedScriptedLoc this._realScriptedLoc

    member this.scriptedLoc
        with set value = this._realScriptedLoc <- value

    member val proccessedLoc: (Lang * Collections.Map<string, LocEntry>) list = [] with get, set
    member val technologies: (string * string list) list = [] with get, set
    member val configRules: RootRule array = [||] with get, set
    member val typeDefs: TypeDefinition list = [] with get, set
    /// Map<enum key, (description * values list)
    member val enumDefs: Map<string, string * (string * range option) array> = Map.empty with get, set
    member val typeDefInfo: Map<string, TypeDefInfo array> = Map.empty with get, set
    member val typeDefInfoForValidation: Map<string, struct (string * range) array> = Map.empty with get, set
    member val varDefInfo: Map<string, (string * range) array> = Map.empty with get, set
    member val extendedConfigMetadata: ExtendedConfigMetadata = ExtendedConfigMetadata.empty with get, set
    member val savedEventTargets: ResizeArray<string * range * Scope> = new ResizeArray<_>() with get, set
    /// Stores scripted variables as (name, value) pairs
    member val scriptedVariables: (string * string) list = [] with get, set
    /// Names of scripted variables that are game-globals (defined under
    /// common/scripted_variables); all other @-variables are file-local.
    member val globalScriptedVariableNames: string list = [] with get, set

    /// Shallow copy for staged (lockless) cache refreshes: the clone shares all current
    /// field values, so a refresh can mutate it freely while readers keep seeing the
    /// original's consistent state.
    member this.ShallowClone() : Lookup = this.MemberwiseClone() :?> Lookup

type JominiLookup() =
    inherit Lookup()
    member val ScriptedEffectKeys: string list = [] with get, set

type CK2Lookup() =
    inherit Lookup()
    member val CK2LandedTitles: Collections.Map<TitleType * bool, string list> = Map.empty with get, set // Title * landless
    member val CK2provinces: string array = [||] with get, set

type EU4Lookup() =
    inherit Lookup()
    member val EU4ScriptedEffectKeys: string array = [||] with get, set
    member val EU4TrueLegacyGovernments: string array = [||] with get, set

type HOI4Lookup() =
    inherit Lookup()
    member val HOI4provinces: string array = [||] with get, set

type STLLookup() =
    inherit Lookup()

type IRLookup() =
    inherit JominiLookup()
    member val IRprovinces: string array = [||] with get, set
    member val IRcharacters: string array = [||] with get, set

type VIC2Lookup() =
    inherit Lookup()
    member val VIC2provinces: string array = [||] with get, set

type Lookup with
    member private this.BaseFieldSnapshot() =
        { allCoreLinks = this.allCoreLinks
          onlyScriptedEffects = this.onlyScriptedEffects
          onlyScriptedTriggers = this.onlyScriptedTriggers
          rootFolders = this.rootFolders
          staticModifiers = this.staticModifiers
          coreModifiers = this.coreModifiers
          embeddedScriptedLoc = this.embeddedScriptedLoc
          realScriptedLoc = this._realScriptedLoc
          proccessedLoc = this.proccessedLoc
          technologies = this.technologies
          configRules = this.configRules
          typeDefs = this.typeDefs
          enumDefs = this.enumDefs
          typeDefInfo = this.typeDefInfo
          typeDefInfoForValidation = this.typeDefInfoForValidation
          varDefInfo = this.varDefInfo
          extendedConfigMetadata = this.extendedConfigMetadata
          savedEventTargets = this.savedEventTargets
          scriptedVariables = this.scriptedVariables
          globalScriptedVariableNames = this.globalScriptedVariableNames }

    /// Capture only explicit source fields produced by a staged refresh. Derived
    /// lazy lists and maps are deliberately excluded.
    member this.CreateFieldSnapshot() =
        let subtype =
            if this.GetType() = typeof<Lookup> then LookupBase
            elif this.GetType() = typeof<IRLookup> then
                let lookup = this :?> IRLookup
                LookupIR(lookup.ScriptedEffectKeys, lookup.IRprovinces, lookup.IRcharacters)
            elif this.GetType() = typeof<JominiLookup> then
                LookupJomini((this :?> JominiLookup).ScriptedEffectKeys)
            elif this.GetType() = typeof<CK2Lookup> then
                let lookup = this :?> CK2Lookup
                LookupCK2(lookup.CK2LandedTitles, lookup.CK2provinces)
            elif this.GetType() = typeof<EU4Lookup> then
                let lookup = this :?> EU4Lookup
                LookupEU4(lookup.EU4ScriptedEffectKeys, lookup.EU4TrueLegacyGovernments)
            elif this.GetType() = typeof<HOI4Lookup> then
                LookupHOI4((this :?> HOI4Lookup).HOI4provinces)
            elif this.GetType() = typeof<STLLookup> then LookupSTL
            elif this.GetType() = typeof<VIC2Lookup> then
                LookupVIC2((this :?> VIC2Lookup).VIC2provinces)
            else
                invalidOp $"Unsupported Lookup subtype: {this.GetType().FullName}"

        { baseFields = this.BaseFieldSnapshot()
          subtype = subtype }

    /// Apply a typed snapshot without changing this lookup object's identity.
    /// Assigning allCoreLinks rebuilds every derived lazy list and map live. The caller
    /// must hold the game-state write lock for the complete guard-and-apply operation.
    member this.ApplyFieldSnapshot(snapshot: LookupFieldSnapshot) =
        let subtypeMatches =
            match snapshot.subtype with
            | LookupBase -> this.GetType() = typeof<Lookup>
            | LookupJomini _ -> this.GetType() = typeof<JominiLookup>
            | LookupCK2 _ -> this.GetType() = typeof<CK2Lookup>
            | LookupEU4 _ -> this.GetType() = typeof<EU4Lookup>
            | LookupHOI4 _ -> this.GetType() = typeof<HOI4Lookup>
            | LookupSTL -> this.GetType() = typeof<STLLookup>
            | LookupIR _ -> this.GetType() = typeof<IRLookup>
            | LookupVIC2 _ -> this.GetType() = typeof<VIC2Lookup>

        if not subtypeMatches then
            invalidArg "snapshot" "Lookup field snapshot has a different runtime type"

        let fields = snapshot.baseFields
        this.allCoreLinks <- fields.allCoreLinks
        this.onlyScriptedEffects <- fields.onlyScriptedEffects
        this.onlyScriptedTriggers <- fields.onlyScriptedTriggers
        this.rootFolders <- fields.rootFolders
        this.staticModifiers <- fields.staticModifiers
        this.coreModifiers <- fields.coreModifiers
        this.embeddedScriptedLoc <- fields.embeddedScriptedLoc
        this._realScriptedLoc <- fields.realScriptedLoc
        this.proccessedLoc <- fields.proccessedLoc
        this.technologies <- fields.technologies
        this.configRules <- fields.configRules
        this.typeDefs <- fields.typeDefs
        this.enumDefs <- fields.enumDefs
        this.typeDefInfo <- fields.typeDefInfo
        this.typeDefInfoForValidation <- fields.typeDefInfoForValidation
        this.varDefInfo <- fields.varDefInfo
        this.extendedConfigMetadata <- fields.extendedConfigMetadata
        this.savedEventTargets <- fields.savedEventTargets
        this.scriptedVariables <- fields.scriptedVariables
        this.globalScriptedVariableNames <- fields.globalScriptedVariableNames

        match snapshot.subtype with
        | LookupBase
        | LookupSTL -> ()
        | LookupJomini scriptedEffectKeys ->
            (this :?> JominiLookup).ScriptedEffectKeys <- scriptedEffectKeys
        | LookupCK2(landedTitles, provinces) ->
            let lookup = this :?> CK2Lookup
            lookup.CK2LandedTitles <- landedTitles
            lookup.CK2provinces <- provinces
        | LookupEU4(scriptedEffectKeys, trueLegacyGovernments) ->
            let lookup = this :?> EU4Lookup
            lookup.EU4ScriptedEffectKeys <- scriptedEffectKeys
            lookup.EU4TrueLegacyGovernments <- trueLegacyGovernments
        | LookupHOI4 provinces ->
            (this :?> HOI4Lookup).HOI4provinces <- provinces
        | LookupIR(scriptedEffectKeys, provinces, characters) ->
            let lookup = this :?> IRLookup
            lookup.ScriptedEffectKeys <- scriptedEffectKeys
            lookup.IRprovinces <- provinces
            lookup.IRcharacters <- characters
        | LookupVIC2 provinces ->
            (this :?> VIC2Lookup).VIC2provinces <- provinces
