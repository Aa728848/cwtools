namespace CWTools.Games

open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.Diagnostics
open System.Linq
open System.Threading
open CWTools.Process
open FSharp.Collections.ParallelSeq
open FParsec
open System.IO
open CWTools.Parser
open DotNet.Globbing
open CWTools.Common.STLConstants
open CWTools.Utilities.Position
open CWTools.Utilities.Utils
open CWTools.Utilities
open CWTools.Utilities.StringResource

module ResourceManagerEager =
    let mutable private eagerVersion = 0

    let nextVersion () =
        Interlocked.Increment(&eagerVersion)

    let currentVersion () = Volatile.Read(&eagerVersion)

// Fuzzy = prefix/suffix
type ReferenceType =
    | TypeDef = 0uy
    | Link = 1uy
    | TypeDefFuzzy = 2uy

type ReferenceDetails =
    { name: StringTokens
      originalValue: StringTokens
      position: range
      isOutgoing: bool
      referenceLabel: string option
      referenceType: ReferenceType
      // Associated type, e.g. with modifiers, the main type is the building, but the associated type is modifier_type
      associatedType: string option }

type ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks, savedEventTargets) =
    member val Cache: Map<string, obj list> = Map.empty with get, set
    member val WithRulesData: bool = withRulesData with get, set
    member val Referencedtypes: Map<string, ReferenceDetails list> option = referencedtypes with get, set
    member val Definedvariables: Map<string, ResizeArray<string * range>> option = definedvariable with get, set

    member val SavedEventTargets: ResizeArray<string * range * CWTools.Common.NewScope.Scope> option =
        savedEventTargets with get, set

    member val EffectBlocks: Node list option = effectBlocks with get, set
    member val TriggerBlocks: Node list option = triggersBlocks with get, set

type EU4ComputedData
    (
        referencedtypes,
        definedvariable,
        scriptedeffectparams,
        withRulesData,
        effectBlocks,
        triggersBlocks,
        savedEventTargets
    ) =
    inherit
        ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks, savedEventTargets)

    member val ScriptedEffectParams: string list option = scriptedeffectparams with get, set
    member val ScriptValueParams: string list option = None with get, set

type HOI4ComputedData = ComputedData
type CK2ComputedData = ComputedData
type VIC2ComputedData = ComputedData

type ScriptedEffectComputedData
    (
        referencedtypes,
        definedvariable,
        scriptedeffectparams,
        withRulesData,
        effectBlocks,
        triggersBlocks,
        savedEventTargets
    ) =
    inherit
        ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks, savedEventTargets)

    member val ScriptedEffectParams: string list option = scriptedeffectparams with get, set
    member val ScriptValueParams: string list option = None with get, set

type STLComputedData = ScriptedEffectComputedData
type JominiComputedData = ScriptedEffectComputedData

type IRComputedData = JominiComputedData
type CK3ComputedData = JominiComputedData
type VIC3ComputedData = JominiComputedData
type EU5ComputedData = JominiComputedData
//     inherit ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks)
// type CK2ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks) =
//     inherit ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks)
// type IRComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks) =
//     inherit ComputedData(referencedtypes, definedvariable, withRulesData, effectBlocks, triggersBlocks)


type PassFileResult = { parseTime: float }

type FailFileResult =
    { error: string
      position: FParsec.Position
      parseTime: float }

type FileResult =
    | Pass of result: PassFileResult
    | Fail of result: FailFileResult
//|Embedded of file : string * statements : Statement list

type Overwrite =
    | No = 1uy
    | Overwrote = 2uy
    | Overwritten = 3uy

type EntityResource =
    { scope: string
      filepath: string
      logicalpath: string
      result: FileResult
      overwrite: Overwrite
      validate: bool }

type FileResource =
    { scope: string
      filepath: string
      logicalpath: string }

type FileWithContentResource =
    { scope: string
      filetext: string
      filepath: string
      logicalpath: string
      overwrite: Overwrite
      validate: bool }

type Resource =
    | EntityResource of string * EntityResource
    | FileResource of string * FileResource
    | FileWithContentResource of string * FileWithContentResource

type EntityResourceInput =
    { scope: string
      filepath: string
      logicalpath: string
      filetext: string
      validate: bool }

type FileResourceInput =
    { scope: string
      filepath: string
      logicalpath: string }

type FileWithContentResourceInput =
    { scope: string
      filetext: string
      filepath: string
      logicalpath: string
      validate: bool }

type Entity =
    { filepath: string
      logicalpath: string
      rawEntity: Node
      entity: Node
      validate: bool
      entityType: EntityType
      overwrite: Overwrite }

    override x.ToString() =
        sprintf "%s %s %b" x.filepath x.logicalpath x.validate

type RawEntity = Entity

type CachedResourceData =
    { resources: (Resource * Entity) list
      files: (string * string) list
      fileIndexTable: FileIndexTable
      stringResourceManager: StringResourceManager }

type ResourceInput =
    | EntityResourceInput of EntityResourceInput
    | FileResourceInput of FileResourceInput
    | CachedResourceInput of Resource * Entity
    | FileWithContentResourceInput of FileWithContentResourceInput

/// Parsed single-file update that has not yet mutated the live resource maps.
/// Parsing is intentionally separated from commit so editor updates only need
/// a short write-locked swap phase.
type PreparedResourceUpdate =
    { parsedResource: Resource
      parsedEntity: Entity option }




type UpdateFile<'T> = ResourceInput -> Resource * struct (Entity * Lazy<'T>) option
type UpdateFiles<'T> = ResourceInput array -> (Resource * struct (Entity * Lazy<'T>) option) list
type RemoveFile = string -> bool
type GetResources = unit -> Resource list
type ValidatableFiles = unit -> EntityResource list
type AllEntities<'T> = unit -> struct (Entity * Lazy<'T>) seq
type ValidatableEntities<'T> = unit -> struct (Entity * Lazy<'T>) list
type FileNames = unit -> string seq

type IResourceAPI<'T when 'T :> ComputedData> =
    abstract UpdateFiles: UpdateFiles<'T>
    abstract UpdateFile: UpdateFile<'T>
    abstract RemoveFile: RemoveFile
    abstract GetResources: GetResources
    abstract ValidatableFiles: ValidatableFiles
    abstract AllEntities: AllEntities<'T>
    abstract ValidatableEntities: ValidatableEntities<'T>
    abstract ForceRecompute: unit -> unit
    abstract ForceDynamicParameterData: int * int -> int
    abstract ForceRulesDataGenerate: unit -> unit
    abstract GetInlineScriptCallers: string -> string list
    abstract RefreshInlineScriptCallers: string list -> string list
    abstract GetFileNames: FileNames
    abstract GetEntityByFilePath: string -> struct (Entity * Lazy<'T>) option

[<Sealed>]
type ResourceManager<'T when 'T :> ComputedData>
    (
        computedDataFunction: Entity -> 'T,
        computedDataUpdateFunction: Entity -> 'T -> unit,
        encoding,
        fallbackencoding,
        enableInlineScripts
    ) =
    static do GlobOptions.Default.Evaluation.CaseInsensitive <- true
    static let globCache = ConcurrentDictionary<string, Glob>()

    let globCheckFilepath (pattern: string) (path: string) =
        match globCache.TryGetValue(pattern) with
        | true, glob -> glob.IsMatch(path)
        | false, _ ->
            let glob = Glob.Parse(pattern)
            globCache.TryAdd(pattern, glob) |> ignore
            glob.IsMatch(path)

    let filepathToEntityType =
        function
        | x when globCheckFilepath "**/common/*.txt" x -> EntityType.Other
        | x when globCheckFilepath "**/common/agendas/*.txt" x -> EntityType.Agenda
        | x when globCheckFilepath "**/common/ambient_objects/*.txt" x -> EntityType.AmbientObjects
        | x when globCheckFilepath "**/common/anomalies/*.txt" x -> EntityType.Anomalies
        | x when globCheckFilepath "**/common/armies/*.txt" x -> EntityType.Armies
        | x when globCheckFilepath "**/common/army_attachments/*.txt" x -> EntityType.ArmyAttachments
        | x when globCheckFilepath "**/common/ascension_perks/*.txt" x -> EntityType.AscensionPerks
        | x when globCheckFilepath "**/common/attitudes/*.txt" x -> EntityType.Attitudes
        | x when globCheckFilepath "**/common/bombardment_stances/*.txt" x -> EntityType.BombardmentStances
        | x when globCheckFilepath "**/common/buildable_pops/*.txt" x -> EntityType.BuildablePops
        | x when globCheckFilepath "**/common/building_tags/*.txt" x -> EntityType.BuildingTags
        | x when globCheckFilepath "**/common/buildings/*.txt" x -> EntityType.Buildings
        | x when globCheckFilepath "**/common/button_effects/*.txt" x -> EntityType.ButtonEffects
        | x when globCheckFilepath "**/common/bypass/*.txt" x -> EntityType.Bypass
        | x when globCheckFilepath "**/common/casus_belli/*.txt" x -> EntityType.CasusBelli
        | x when globCheckFilepath "**/common/colors/*.txt" x -> EntityType.Colors
        | x when globCheckFilepath "**/common/component_flags/*.txt" x -> EntityType.ComponentFlags
        | x when globCheckFilepath "**/common/component_sets/*.txt" x -> EntityType.ComponentSets
        | x when globCheckFilepath "**/common/component_tags/*.txt" x -> EntityType.ComponentTags
        | x when globCheckFilepath "**/common/component_templates/*.txt" x -> EntityType.ComponentTemplates
        | x when globCheckFilepath "**/common/country_customization/*.txt" x -> EntityType.CountryCustomization
        | x when globCheckFilepath "**/common/country_types/*.txt" x -> EntityType.CountryTypes
        | x when globCheckFilepath "**/common/decisions/*.txt" x -> EntityType.Decisions
        | x when globCheckFilepath "**/common/deposits/*.txt" x -> EntityType.Deposits
        | x when globCheckFilepath "**/common/diplo_phrases/*.txt" x -> EntityType.DiploPhrases
        | x when globCheckFilepath "**/common/diplomatic_actions/*.txt" x -> EntityType.DiplomaticActions
        | x when globCheckFilepath "**/common/edicts/*.txt" x -> EntityType.Edicts
        | x when globCheckFilepath "**/common/ethics/*.txt" x -> EntityType.Ethics
        | x when globCheckFilepath "**/common/event_chains/*.txt" x -> EntityType.EventChains
        | x when globCheckFilepath "**/common/fallen_empires/*.txt" x -> EntityType.FallenEmpires
        | x when globCheckFilepath "**/common/game_rules/*.txt" x -> EntityType.GameRules
        | x when globCheckFilepath "**/common/global_ship_designs/*.txt" x -> EntityType.GlobalShipDesigns
        | x when globCheckFilepath "**/common/governments/*.txt" x -> EntityType.Governments
        | x when globCheckFilepath "**/common/governments/authorities/*.txt" x -> EntityType.Authorities
        | x when globCheckFilepath "**/common/governments/civics/*.txt" x -> EntityType.Civics
        | x when globCheckFilepath "**/common/graphical_culture/*.txt" x -> EntityType.GraphicalCulture
        | x when globCheckFilepath "**/common/mandates/*.txt" x -> EntityType.Mandates
        | x when globCheckFilepath "**/common/map_modes/*.txt" x -> EntityType.MapModes
        | x when globCheckFilepath "**/common/megastructures/*.txt" x -> EntityType.Megastructures
        | x when globCheckFilepath "**/common/name_lists/*.txt" x -> EntityType.NameLists
        | x when globCheckFilepath "**/common/notification_modifiers/*.txt" x -> EntityType.NotificationModifiers
        | x when globCheckFilepath "**/common/observation_station_missions/*.txt" x ->
            EntityType.ObservationStationMissions
        | x when globCheckFilepath "**/common/on_actions/*.txt" x -> EntityType.OnActions
        | x when globCheckFilepath "**/common/opinion_modifiers/*.txt" x -> EntityType.OpinionModifiers
        | x when globCheckFilepath "**/common/personalities/*.txt" x -> EntityType.Personalities
        | x when globCheckFilepath "**/common/planet_classes/*.txt" x -> EntityType.PlanetClasses
        | x when globCheckFilepath "**/common/planet_modifiers/*.txt" x -> EntityType.PlanetModifiers
        | x when globCheckFilepath "**/common/policies/*.txt" x -> EntityType.Policies
        | x when globCheckFilepath "**/common/pop_faction_types/*.txt" x -> EntityType.PopFactionTypes
        | x when globCheckFilepath "**/common/precursor_civilizations/*.txt" x -> EntityType.PrecursorCivilizations
        | x when globCheckFilepath "**/common/scripted_effects/*.txt" x -> EntityType.ScriptedEffects
        | x when globCheckFilepath "**/common/scripted_loc/*.txt" x -> EntityType.ScriptedLoc
        | x when globCheckFilepath "**/common/scripted_triggers/*.txt" x -> EntityType.ScriptedTriggers
        | x when globCheckFilepath "**/common/scripted_variables/*.txt" x -> EntityType.ScriptedVariables
        | x when globCheckFilepath "**/common/section_templates/*.txt" x -> EntityType.SectionTemplates
        | x when globCheckFilepath "**/common/sector_types/*.txt" x -> EntityType.SectorTypes
        | x when globCheckFilepath "**/common/ship_behaviors/*.txt" x -> EntityType.ShipBehaviors
        | x when globCheckFilepath "**/common/ship_sizes/*.txt" x -> EntityType.ShipSizes
        | x when globCheckFilepath "**/common/solar_system_initializers/**/*.txt" x ->
            EntityType.SolarSystemInitializers
        | x when globCheckFilepath "**\\common\\solar_system_initializers\\**\\*.txt" x ->
            EntityType.SolarSystemInitializers
        | x when globCheckFilepath "**/common/solar_system_initializers/*.txt" x -> EntityType.SolarSystemInitializers
        | x when globCheckFilepath "**/common/special_projects/*.txt" x -> EntityType.SpecialProjects
        | x when globCheckFilepath "**/common/species_archetypes/*.txt" x -> EntityType.SpeciesArchetypes
        | x when globCheckFilepath "**/common/species_classes/*.txt" x -> EntityType.SpeciesClasses
        | x when globCheckFilepath "**/common/species_names/*.txt" x -> EntityType.SpeciesNames
        | x when globCheckFilepath "**/common/species_rights/*.txt" x -> EntityType.SpeciesRights
        | x when globCheckFilepath "**/common/star_classes/*.txt" x -> EntityType.StarClasses
        | x when globCheckFilepath "**/common/starbase_buildings/*.txt" x -> EntityType.StarbaseBuilding
        | x when globCheckFilepath "**/common/starbase_levels/*.txt" x -> EntityType.StarbaseLevels
        | x when globCheckFilepath "**/common/starbase_modules/*.txt" x -> EntityType.StarbaseModules
        | x when globCheckFilepath "**/common/starbase_types/*.txt" x -> EntityType.StarbaseTypes
        | x when globCheckFilepath "**/common/spaceport_modules/*.txt" x -> EntityType.SpaceportModules
        | x when globCheckFilepath "**/common/start_screen_messages/*.txt" x -> EntityType.StartScreenMessages
        | x when globCheckFilepath "**/common/static_modifiers/*.txt" x -> EntityType.StaticModifiers
        | x when globCheckFilepath "**/common/strategic_resources/*.txt" x -> EntityType.StrategicResources
        | x when globCheckFilepath "**/common/subjects/*.txt" x -> EntityType.Subjects
        | x when globCheckFilepath "**/common/system_types/*.txt" x -> EntityType.SystemTypes
        | x when globCheckFilepath "**/common/technology/*.txt" x -> EntityType.Technology
        | x when globCheckFilepath "**/common/terraform/*.txt" x -> EntityType.Terraform
        | x when globCheckFilepath "**/common/tile_blockers/*.txt" x -> EntityType.TileBlockers
        | x when globCheckFilepath "**/common/tradition_categories/*.txt" x -> EntityType.TraditionCategories
        | x when globCheckFilepath "**/common/traditions/*.txt" x -> EntityType.Traditions
        | x when globCheckFilepath "**/common/traits/*.txt" x -> EntityType.Traits
        | x when globCheckFilepath "**/common/triggered_modifiers/*.txt" x -> EntityType.TriggeredModifiers
        | x when globCheckFilepath "**/common/war_demand_counters/*.txt" x -> EntityType.WarDemandCounters
        | x when globCheckFilepath "**/common/war_demand_types/*.txt" x -> EntityType.WarDemandTypes
        | x when globCheckFilepath "**/common/war_goals/*.txt" x -> EntityType.WarGoals
        | x when globCheckFilepath "**/events/*.txt" x -> EntityType.Events
        | x when globCheckFilepath "**/events/**/*.txt" x -> EntityType.Events
        | x when globCheckFilepath "**\\events\\**\\*.txt" x -> EntityType.Events
        | x when globCheckFilepath "**/map/galaxy/*.txt" x -> EntityType.MapGalaxy
        | x when globCheckFilepath "**/map/setup_scenarios/*.txt" x -> EntityType.MapSetupScenarios
        | x when globCheckFilepath "**/prescripted_countries/*.txt" x -> EntityType.PrescriptedCountries
        | x when globCheckFilepath "**/interface/**/*.gfx" x -> EntityType.Interface
        | x when globCheckFilepath "**\\interface\\**\\*.gfx" x -> EntityType.Interface
        | x when globCheckFilepath "**/interface/**/*.gui" x -> EntityType.Interface
        | x when globCheckFilepath "**\\interface\\**\\*.gui" x -> EntityType.Interface
        | x when globCheckFilepath "**/interface/*.gfx" x -> EntityType.Interface
        | x when globCheckFilepath "**/interface/*.gui" x -> EntityType.Interface
        | x when globCheckFilepath "**/gfx/**/*.gfx" x -> EntityType.GfxGfx
        | x when globCheckFilepath "**\\gfx\\**\\*.gfx" x -> EntityType.GfxGfx
        | x when globCheckFilepath "**/gfx/*.gfx" x -> EntityType.GfxGfx
        | x when globCheckFilepath "**/gfx/**/*.asset" x -> EntityType.GfxAsset
        | x when globCheckFilepath "**\\gfx\\**\\*.asset" x -> EntityType.GfxAsset
        | x when globCheckFilepath "**/gfx/*.asset" x -> EntityType.GfxAsset
        | _ -> EntityType.Other

    let fileMap = Dictionary<string, Resource>(52361)

    /// Key: filePath
    let entitiesMap = Dictionary<string, struct (Entity * Lazy<'T>)>(5306)

    let duration f =
        let timestamp = Stopwatch.GetTimestamp()
        let returnValue = f ()
        (returnValue, Stopwatch.GetElapsedTime(timestamp).TotalMilliseconds)

    let matchResult (scope: string, file: string, logicalpath: string, validate: bool, (parseResult, time)) =
        match parseResult with
        | Success(parsed, _, _) ->
            EntityResource(
                file,
                { scope = scope
                  filepath = file
                  logicalpath = logicalpath
                  validate = validate
                  result = Pass({ parseTime = time })
                  overwrite = Overwrite.No }
            ),
            parsed
        | Failure(msg, pe, _) ->
            EntityResource(
                file,
                { scope = scope
                  filepath = file
                  logicalpath = logicalpath
                  validate = validate
                  result =
                    Fail(
                        { error = msg
                          position = pe.Position
                          parseTime = time }
                    )
                  overwrite = Overwrite.No }
            ),
            []

    let shipProcess = STLProcess.shipProcess.ProcessNode

    let parseEntity ((file, statements): Resource * Statement list) =
        file,
        match file with
        | EntityResource(_,
                         { result = Pass _
                           filepath = f
                           validate = v
                           logicalpath = l }) ->
            let entityType = filepathToEntityType f
            let filename = Path.GetFileNameWithoutExtension f
            let entity = (shipProcess entityType filename (mkZeroFile f) statements)

            Some
                { filepath = f
                  logicalpath = l
                  entity = entity
                  rawEntity = entity
                  validate = v
                  entityType = entityType
                  overwrite = Overwrite.No }
        | _ -> None

    let parseFileInner (filetext: string) (filename: string) =
        // `filetext` is already a decoded .NET string. Re-encoding it after a parse
        // failure cannot recover the original bytes and replaces characters that
        // are not representable in the fallback code page (for example CJK text)
        // with `?`, which can turn a genuine parse failure into corrupt AST data.
        CKParser.parseString filetext (System.String.Intern(filename))

    let parseFileThenEntity (file: ResourceInput) =
        match file with
        | CachedResourceInput(r, e) -> r, Some e
        | EntityResourceInput e ->
            // log "%A %A" e.logicalpath e.filepath
            e
            |> ((fun f ->
                    f.scope,
                    f.filepath,
                    f.logicalpath,
                    f.validate,
                    (fun (t, t2) -> duration (fun () -> parseFileInner t2 (System.String.Intern(t)))) (
                        f.filepath,
                        f.filetext
                    ))
                >> matchResult)
            |> parseEntity
        | FileResourceInput f ->
            (FileResource(
                f.filepath,
                { scope = f.scope
                  filepath = f.filepath
                  logicalpath = f.logicalpath }
             ),
             [])
            |> parseEntity
        | FileWithContentResourceInput f ->
            (FileWithContentResource(
                f.filepath,
                { scope = f.scope
                  filepath = f.filepath
                  logicalpath = f.logicalpath
                  filetext = f.filetext
                  overwrite = Overwrite.No
                  validate = f.validate }
             ),
             [])
            |> parseEntity


    let saveResults (resource, entity) =
        seq {
            match resource with
            | EntityResource(f, _) -> fileMap[f] <- resource
            | FileResource(f, _) -> fileMap[f] <- resource
            | FileWithContentResource(f, _) -> fileMap[f] <- resource

            match entity with
            | Some e ->
                let lazyi =
                    new System.Lazy<_>((fun () -> computedDataFunction e), LazyThreadSafetyMode.PublicationOnly)

                let item = struct (e, lazyi)
                // log "e %A %A %A" e.filepath e.logicalpath e.overwrite
                entitiesMap[e.filepath] <- item
                yield resource, Some item
            | None -> yield resource, None
        }

    let updateOverwrite () =
        let fileList = fileMap.Values.ToArray()

        let entities =
            fileList
            |> Array.choose (function
                | EntityResource(s, e) -> Some((s, e))
                | _ -> None)

        let processGroup (key, es: (string * EntityResource) array) =
            match es with
            | [| s, e |] -> [| s, { e with overwrite = Overwrite.No } |]
            | es ->
                let sorted =
                    es
                    |> Array.sortByDescending (fun (s, e) ->
                        if e.scope = "embedded" then ""
                        else if e.scope = "" then "ZZZZZZZZ"
                        else e.scope)

                let firstStr, entity = sorted[0]

                sorted[0] <-
                    (firstStr,
                     { entity with
                         overwrite = Overwrite.Overwrote })

                for i in 1 .. sorted.Length - 1 do
                    let s, entity = sorted[i]

                    sorted[i] <-
                        (s,
                         { entity with
                             overwrite = Overwrite.Overwritten })

                sorted

        let res =
            entities
            |> Array.groupBy (fun (_, e) -> e.logicalpath)
            |> Array.collect processGroup

        res |> Array.iter (fun (s, e) -> fileMap[s] <- EntityResource(s, e))

        let entityMap (filePath, e: EntityResource) =
            let found, result = entitiesMap.TryGetValue(filePath)

            if found then
                let struct (olde, oldl) = result

                entitiesMap[filePath] <-
                    struct ({ olde with
                                Entity.overwrite = e.overwrite },
                            oldl)

        res |> Array.iter entityMap

        let filesWithContent =
            fileList
            |> Array.choose (function
                | FileWithContentResource(s, e) -> Some((s, e))
                | _ -> None)

        let processGroup (key, es: (string * FileWithContentResource) array) =
            match es with
            | [| s, e |] -> [| s, { e with overwrite = Overwrite.No } |]
            | es ->
                let sorted =
                    es
                    |> Array.sortByDescending (fun (s, e) ->
                        if e.scope = "embedded" then ""
                        else if e.scope = "" then "ZZZZZZZZ"
                        else e.scope)

                let firstStr, entity = sorted[0]

                sorted[0] <-
                    (firstStr,
                     { entity with
                         overwrite = Overwrite.Overwrote })

                for i in 1 .. sorted.Length - 1 do
                    let s, entity = sorted[i]

                    sorted[i] <-
                        (s,
                         { entity with
                             overwrite = Overwrite.Overwritten })

                sorted

        let res =
            filesWithContent
            |> Array.groupBy (fun (s, e) -> e.logicalpath)
            |> Array.collect processGroup

        res |> Array.iter (fun (s, e) -> fileMap[s] <- FileWithContentResource(s, e))

    // log "print all"
    // entitiesMap |> Map.toList |> List.map fst |> List.sortBy id |> List.iter (log "%s")

    // 性能优化：缓存参数化 inline_script 名称的正则表达式，避免重复编译
    let regexCache = ConcurrentDictionary<string, System.Text.RegularExpressions.Regex>()

    /// 缓存 inline_script 文件的 Map，避免每次 updateInlineScripts 都遍历整个 entitiesMap
    let mutable cachedInlineScriptsMap: Map<string, Node> option = None
    let inlinePath = "common/inline_scripts/"
    let inlinePathLength = inlinePath.Length

    let normalizeInlineScriptPath (path: string) =
        if path.EndsWith(".txt", StringComparison.OrdinalIgnoreCase) then
            path.Substring(0, path.Length - 4)
        else
            path

    let inlineParameterPattern =
        System.Text.RegularExpressions.Regex(@"\$([^$|]+)(?:\|([^$]*))?\$", System.Text.RegularExpressions.RegexOptions.Compiled)

    let inlinePathDefaultPattern =
        System.Text.RegularExpressions.Regex(@"\$[^$|]+\|[^$]*\$", System.Text.RegularExpressions.RegexOptions.Compiled)

    let inlineSimpleParameterPattern =
        System.Text.RegularExpressions.Regex(@"\$([^$|]+)\$", System.Text.RegularExpressions.RegexOptions.Compiled)

    let inlineArithmeticExpressionPattern =
        System.Text.RegularExpressions.Regex(@"@\[\s*(.*?)\s*\]", System.Text.RegularExpressions.RegexOptions.Compiled)

    let inlineParameterName (text: string) =
        let pipeIndex = text.IndexOf('|')
        if pipeIndex >= 0 then text.Substring(0, pipeIndex) else text

    let normalizeInlineParameterKey (key: string) =
        key.Trim().Trim('$') |> inlineParameterName

    let replaceInlineParameters (parameters: (string * string) seq) (text: string) =
        let values =
            parameters
            |> Seq.choose (fun (key, value) ->
                let name = normalizeInlineParameterKey key
                if String.IsNullOrWhiteSpace name then None else Some(name, value))
            |> Map.ofSeq

        inlineParameterPattern.Replace(
            text,
            System.Text.RegularExpressions.MatchEvaluator(fun m ->
                let name = m.Groups.[1].Value
                match values |> Map.tryFind name with
                | Some value -> value
                | None when m.Groups.[2].Success -> m.Groups.[2].Value
                | None -> m.Value)
        )

    let replaceInlineParametersWithoutDefaults (parameters: (string * string) seq) (text: string) =
        let values =
            parameters
            |> Seq.choose (fun (key, value) ->
                let name = normalizeInlineParameterKey key
                if String.IsNullOrWhiteSpace name then None else Some(name, value))
            |> Map.ofSeq

        inlineSimpleParameterPattern.Replace(
            text,
            System.Text.RegularExpressions.MatchEvaluator(fun m ->
                let name = m.Groups.[1].Value
                match values |> Map.tryFind name with
                | Some value -> value
                | None -> m.Value)
        )

    let rec collectScriptedVariableValuesFromNode (node: Node) =
        [ yield!
              node.Leaves
              |> Seq.choose (fun leaf ->
                  if leaf.Key.StartsWith("@", StringComparison.Ordinal)
                     && not (leaf.Key.StartsWith("@[", StringComparison.Ordinal))
                     && not (leaf.Key.StartsWith(@"@\[", StringComparison.Ordinal)) then
                      Some(leaf.Key, leaf.Value.ToRawString().Trim('"'))
                  else
                      None)
          yield! node.Nodes |> Seq.collect collectScriptedVariableValuesFromNode ]

    let collectScriptedVariableValues () =
        entitiesMap.Values
        |> Seq.map structFst
        |> Seq.filter (fun e ->
            e.overwrite <> Overwrite.Overwritten
            && e.logicalpath.Replace('\\', '/').Contains("common/scripted_variables/", StringComparison.OrdinalIgnoreCase))
        |> Seq.collect (fun e -> collectScriptedVariableValuesFromNode e.rawEntity)
        |> Seq.distinctBy fst
        |> Map.ofSeq

    let tryEvaluateInlineArithmeticExpression (variableValues: Map<string, string>) (expression: string) =
        let text = expression.Trim()
        let mutable index = 0

        let skipWs () =
            while index < text.Length && Char.IsWhiteSpace text.[index] do
                index <- index + 1

        let tryParseNumber () =
            skipWs ()
            let start = index

            while index < text.Length && (Char.IsDigit text.[index] || text.[index] = '.') do
                index <- index + 1

            if index = start then
                None
            else
                match Decimal.TryParse(text.Substring(start, index - start), Globalization.NumberStyles.Number, Globalization.CultureInfo.InvariantCulture) with
                | true, value -> Some value
                | _ -> None

        let tryReadVariableName () =
            skipWs ()
            let start = index

            if index < text.Length && text.[index] = '@' then
                index <- index + 1

            if index < text.Length && (Char.IsLetter text.[index] || text.[index] = '_') then
                index <- index + 1

                while
                    index < text.Length
                    && (Char.IsLetterOrDigit text.[index]
                        || text.[index] = '_'
                        || text.[index] = '.'
                        || text.[index] = ':')
                    do
                    index <- index + 1

                let name = text.Substring(start, index - start)
                if name.StartsWith("@", StringComparison.Ordinal) then name else "@" + name
                |> Some
            else
                index <- start
                None

        let tryVariableValue name =
            variableValues
            |> Map.tryFind name
            |> Option.bind (fun raw ->
                match Decimal.TryParse(raw.Trim().Trim('"'), Globalization.NumberStyles.Number, Globalization.CultureInfo.InvariantCulture) with
                | true, value -> Some value
                | _ -> None)

        let rec parseExpression () : decimal option = parseAddSub ()

        and parseAddSub () : decimal option =
            let mutable left: decimal option = parseMulDivMod ()
            skipWs ()

            while left.IsSome && index < text.Length && (text.[index] = '+' || text.[index] = '-') do
                let op = text.[index]
                index <- index + 1
                let right = parseMulDivMod ()
                left <-
                    match left, right with
                    | Some l, Some r -> Some(if op = '+' then l + r else l - r)
                    | _ -> None
                skipWs ()

            left

        and parseMulDivMod () : decimal option =
            let mutable left: decimal option = parseUnary ()
            skipWs ()

            while left.IsSome && index < text.Length && (text.[index] = '*' || text.[index] = '/' || text.[index] = '%') do
                let op = text.[index]
                index <- index + 1
                let right = parseUnary ()
                left <-
                    match left, right with
                    | Some l, Some r when op = '/' && r = 0M -> None
                    | Some l, Some r when op = '%' && r = 0M -> None
                    | Some l, Some r ->
                        match op with
                        | '*' -> Some(l * r)
                        | '/' -> Some(l / r)
                        | '%' -> Some(l % r)
                        | _ -> None
                    | _ -> None
                skipWs ()

            left

        and parseUnary () : decimal option =
            skipWs ()

            if index < text.Length && text.[index] = '+' then
                index <- index + 1
                parseUnary ()
            elif index < text.Length && text.[index] = '-' then
                index <- index + 1
                parseUnary () |> Option.map (fun value -> -value)
            else
                parsePrimary ()

        and parsePrimary () : decimal option =
            skipWs ()

            if index < text.Length && text.[index] = '(' then
                index <- index + 1
                let value = parseExpression ()
                skipWs ()

                if index < text.Length && text.[index] = ')' then
                    index <- index + 1
                    value
                else
                    None
            else
                match tryParseNumber () with
                | Some _ as value -> value
                | None ->
                    tryReadVariableName ()
                    |> Option.bind tryVariableValue

        let result = parseExpression ()
        skipWs ()
        if index = text.Length then result else None

    let evaluateInlineArithmeticExpressions (variableValues: Map<string, string>) (text: string) =
        inlineArithmeticExpressionPattern.Replace(
            text,
            System.Text.RegularExpressions.MatchEvaluator(fun m ->
                match tryEvaluateInlineArithmeticExpression variableValues m.Groups.[1].Value with
                | Some value -> value.ToString("G29", Globalization.CultureInfo.InvariantCulture)
                | None -> m.Value)
        )

    let getOrBuildInlineScriptsMap () =
        match cachedInlineScriptsMap with
        | Some m -> m
        | None ->
            let m =
                entitiesMap.Values
                |> Seq.filter (fun struct (e, _) -> e.overwrite <> Overwrite.Overwritten)
                |> Seq.map structFst
                |> Seq.filter (fun e -> e.logicalpath.StartsWith(inlinePath, StringComparison.OrdinalIgnoreCase))
                |> Seq.map (fun e ->
                    ((normalizeInlineScriptPath (e.logicalpath.Substring inlinePathLength)).ToLowerInvariant(),
                     e.rawEntity))
                |> Map.ofSeq
            cachedInlineScriptsMap <- Some m
            m

    /// 使缓存失效（当 inline_script 文件本身变更时调用）
    let invalidateInlineScriptsCache () = cachedInlineScriptsMap <- None

    let inlineScriptCallerIndex =
        ConcurrentDictionary<string, System.Collections.Generic.HashSet<string>>()
    let inlineScriptCallerKeysByFile = ConcurrentDictionary<string, string array>()

    let normalizeCallerRefKey (s: string) =
        (normalizeInlineScriptPath (s.Replace('\\', '/'))).Trim().ToLowerInvariant()

    let collectInlineScriptRefs (node: Node) =
        let rec collect (n: Node) acc =
            let acc =
                n.Leaves
                |> Seq.fold (fun a (l: Leaf) ->
                    if l.Key.Equals("inline_script", StringComparison.OrdinalIgnoreCase) then
                        let v = l.ValueText
                        if String.IsNullOrWhiteSpace v then a else normalizeCallerRefKey v :: a
                    else a) acc
            n.Nodes
            |> Seq.fold (fun a (child: Node) ->
                let a =
                    if child.Key.Equals("inline_script", StringComparison.OrdinalIgnoreCase) then
                        let s = child.TagText "script"
                        if String.IsNullOrWhiteSpace s then a else normalizeCallerRefKey s :: a
                    else a
                collect child a) acc
        collect node [] |> List.distinct

    let removeCallerContributions (filepath: string) =
        match inlineScriptCallerKeysByFile.TryGetValue filepath with
        | true, keys ->
            for key in keys do
                match inlineScriptCallerIndex.TryGetValue key with
                | true, set ->
                    lock set (fun () ->
                        set.Remove filepath |> ignore
                        if set.Count = 0 then
                            inlineScriptCallerIndex.TryRemove key |> ignore)
                | _ -> ()
            inlineScriptCallerKeysByFile.TryRemove filepath |> ignore
        | _ -> ()

    let isInlineScriptEntity (e: Entity) =
        e.logicalpath.StartsWith(inlinePath, StringComparison.OrdinalIgnoreCase)

    let tryInlineScriptNameForEntity (e: Entity) =
        if isInlineScriptEntity e then
            Some(normalizeCallerRefKey (e.logicalpath.Substring inlinePathLength))
        else
            None

    let addCallerContributions (e: Entity) =
        let keys = collectInlineScriptRefs e.rawEntity
        if not (List.isEmpty keys) then
            inlineScriptCallerKeysByFile[e.filepath] <- List.toArray keys
            for key in keys do
                let set =
                    inlineScriptCallerIndex.GetOrAdd(key, fun _ -> System.Collections.Generic.HashSet<string>())
                lock set (fun () -> set.Add e.filepath |> ignore)

    /// 全量重建反向索引（首次载入后调用）。
    let rebuildInlineScriptCallerIndex () =
        inlineScriptCallerIndex.Clear()
        inlineScriptCallerKeysByFile.Clear()
        for struct (e, _) in entitiesMap.Values do
            addCallerContributions e

    /// 单文件增量更新：先回收旧贡献，再加入当前引用。
    let updateInlineScriptCallerIndexForFile (e: Entity) =
        removeCallerContributions e.filepath
        addCallerContributions e

    let callerPatternRegexCache =
        ConcurrentDictionary<string, System.Text.RegularExpressions.Regex>()

    let inlinePatternKeyToRegex (key: string) =
        callerPatternRegexCache.GetOrAdd(
            key,
            fun k ->
                let sb = System.Text.StringBuilder()
                sb.Append("(?:^|/)") |> ignore
                let mutable lastIndex = 0
                for m in inlineParameterPattern.Matches k do
                    sb.Append(System.Text.RegularExpressions.Regex.Escape(k.Substring(lastIndex, m.Index - lastIndex)))
                    |> ignore
                    sb.Append("[^/]*") |> ignore
                    lastIndex <- m.Index + m.Length
                sb.Append(System.Text.RegularExpressions.Regex.Escape(k.Substring lastIndex)) |> ignore
                sb.Append("$") |> ignore
                System.Text.RegularExpressions.Regex(
                    sb.ToString(),
                    System.Text.RegularExpressions.RegexOptions.Compiled))

    let getDirectInlineScriptCallers (scriptName: string) =
        let target = normalizeCallerRefKey scriptName
        if String.IsNullOrWhiteSpace target then
            []
        else
            let result = System.Collections.Generic.HashSet<string>()
            for kv in inlineScriptCallerIndex do
                let key = kv.Key
                let matched =
                    key = target
                    || key.EndsWith("/" + target, StringComparison.Ordinal)
                    || target.EndsWith("/" + key, StringComparison.Ordinal)
                    || (key.Contains "$"
                        && try (inlinePatternKeyToRegex key).IsMatch target with _ -> false)
                if matched then
                    lock kv.Value (fun () ->
                        for f in kv.Value do
                            result.Add f |> ignore)
            result |> List.ofSeq

    let getInlineScriptCallers (scriptName: string) =
        let result = System.Collections.Generic.HashSet<string>()
        let visitedScripts = System.Collections.Generic.HashSet<string>()

        let rec visit script =
            let target = normalizeCallerRefKey script
            if not (String.IsNullOrWhiteSpace target) && visitedScripts.Add target then
                for caller in getDirectInlineScriptCallers target do
                    match entitiesMap.TryGetValue caller with
                    | true, struct (e, _) ->
                        match tryInlineScriptNameForEntity e with
                        | Some callerScript -> visit callerScript
                        | None -> result.Add caller |> ignore
                    | _ -> result.Add caller |> ignore

        visit scriptName
        result |> List.ofSeq

    let updateInlineScripts (news: (Resource * struct (Entity * Lazy<'T>) option) list) =
        // 如果被修改的文件是 inline_script 本身，先失效缓存
        for (resource, entityOpt) in news do
            match entityOpt with
            | Some struct (e, _) when e.logicalpath.StartsWith(inlinePath, StringComparison.OrdinalIgnoreCase) -> invalidateInlineScriptsCache ()
            | _ -> ()

        let inlineScriptsMap = getOrBuildInlineScriptsMap ()
        let scriptedVariableValues = lazy (collectScriptedVariableValues ())

        // Helper: try exact match first, then suffix match, then wildcard match for $PARAM$ patterns
        let tryFindInlineScript (scriptName: string) =
            let scriptName =
                if scriptName.Contains("@[", StringComparison.Ordinal) then
                    evaluateInlineArithmeticExpressions scriptedVariableValues.Value scriptName
                else
                    scriptName

            let lookupName = (normalizeInlineScriptPath (scriptName.Replace('\\', '/'))).ToLowerInvariant()
            match inlineScriptsMap |> Map.tryFind lookupName with
            | Some _ as result -> result
            | None ->
                let normalizedName = lookupName

                // Check if scriptName contains parameter patterns like $RARITY$
                let hasParams = normalizedName.Contains("$")
                let hasPathDefault = inlinePathDefaultPattern.IsMatch normalizedName

                // 性能优化：使用缓存的正则表达式，避免重复编译
                let pattern =
                    if hasParams then
                        regexCache.GetOrAdd(normalizedName, fun name ->
                            let parts = name.Split('$')
                            let patternStr =
                                parts
                                |> Array.mapi (fun i part ->
                                    if i % 2 = 1 then // odd indices are inside $...$
                                        "(.+)"
                                    else
                                        System.Text.RegularExpressions.Regex.Escape(part))
                                |> String.concat ""
                            System.Text.RegularExpressions.Regex("^" + patternStr + "$", System.Text.RegularExpressions.RegexOptions.Compiled))
                    else
                        null

                inlineScriptsMap
                |> Map.tryPick (fun key value ->
                    let normalizedKey = key.Replace('\\', '/')
                    // Suffix match（键与 normalizedName 均已小写；用 Ordinal 避免区域文化敏感比较带来的跨平台/跨 locale 差异）
                    if normalizedKey.EndsWith("/" + normalizedName, StringComparison.Ordinal)
                       || normalizedName.EndsWith("/" + normalizedKey, StringComparison.Ordinal) then
                        Some value
                    // Wildcard match for parameterized script names
                    elif hasParams && not hasPathDefault && pattern.IsMatch(normalizedKey) then
                        Some value
                    else
                        None)

        let keyId = StringResource.stringManager.InternIdentifierToken "inline_script"
        let keyIdLower = keyId.lower
        let scriptKeyId = StringResource.stringManager.InternIdentifierToken "script"
        let scriptKeyIdLower = scriptKeyId.lower

        // 性能优化：快速判断 AST 是否包含 inline_script 引用（可提前退出，比 foldNode7 快得多）
        let rec containsInlineScriptRef (node: Node) =
            // 检查节点自身的 key 是否是 inline_script
            if node.KeyId.lower = keyIdLower then true
            // 检查直接子元素中是否有 inline_script 引用（不递归）
            elif node.AllArray |> Array.exists (function
                | NodeC n -> n.KeyId.lower = keyIdLower
                | LeafC l -> l.KeyId.lower = keyIdLower
                | _ -> false)
            then true
            // 递归检查子节点
            else node.Nodes |> Seq.exists containsInlineScriptRef

        let folder (node: Node) (acc: Child list) =
            if node.KeyId.lower = keyIdLower then
                NodeC node :: acc
            else
                node.LeafsById keyIdLower |> Seq.fold (fun state x -> LeafC x :: state) acc

        let updateEntity (e: Entity) =
            // 性能优化：快速短路检查，如果实体不包含任何 inline_script 引用则直接跳过
            if not (containsInlineScriptRef e.entity) then
                None
            else

            let allScriptRefs = ProcessCore.foldNode7 folder e.entity
            // allScriptRefs |> List.iter (function |LeafC l -> log $"a {l.ValueText} {l.Position}" |_ -> ())
            let nodeScriptRefs =
                allScriptRefs
                |> List.choose (function
                    | NodeC n -> Some n
                    | _ -> None)

            let leafScriptRefs =
                allScriptRefs
                |> List.choose (function
                    | LeafC l -> Some l
                    | _ -> None)

            // 性能优化：将 List.exists 替换为 HashSet 查找（O(N) -> O(1)）
            let nodeRefSet = HashSet<struct(int * int * int * int * StringLowerToken)>()
            for s in nodeScriptRefs do
                nodeRefSet.Add(struct(s.Position.StartLine, s.Position.StartColumn, s.Position.EndLine, s.Position.EndColumn, s.KeyId.lower)) |> ignore

            let leafRefSet = HashSet<struct(int * int * int * int * StringLowerToken * StringLowerToken)>()
            for s in leafScriptRefs do
                leafRefSet.Add(struct(s.Position.StartLine, s.Position.StartColumn, s.Position.EndLine, s.Position.EndColumn, s.KeyId.lower, s.ValueId.lower)) |> ignore

            let rec replaceCataFun (node: Node) =
                let childFun (child: Child) =
                    let triviaFor originalPosition =
                        Some { originalSource = Some originalPosition }

                    let rec addDescendantLeafTrivia originalPosition =
                        function
                        | NodeC n -> n.AllArray |> Array.iter (addDescendantLeafTrivia originalPosition)
                        | ValueClauseC vc -> vc.AllArray |> Array.iter (addDescendantLeafTrivia originalPosition)
                        | LeafC l -> l.Trivia <- triviaFor originalPosition
                        | LeafValueC lv -> lv.Trivia <- triviaFor originalPosition
                        | CommentC _ -> ()

                    let addTrivia originalPosition =
                        function
                        | NodeC n ->
                            n.Trivia <- triviaFor originalPosition
                            n.AllArray |> Array.iter (addDescendantLeafTrivia originalPosition)
                        | LeafC l -> l.Trivia <- triviaFor originalPosition
                        | LeafValueC lv -> lv.Trivia <- triviaFor originalPosition
                        | ValueClauseC vc ->
                            vc.Trivia <- triviaFor originalPosition
                            vc.AllArray |> Array.iter (addDescendantLeafTrivia originalPosition)
                        | CommentC _ -> ()

                    match child with
                    | NodeC n ->
                        let stringReplace (isParams: (string * string) seq) (key: string) =
                            replaceInlineParameters isParams key

                        let stringReplaceWithoutDefaults (isParams: (string * string) seq) (key: string) =
                            replaceInlineParametersWithoutDefaults isParams key

                        let rec foldOverNode stringReplacer inlineScriptPathReplacer (node: Node) =
                            node.Key <- stringReplacer node.Key

                            let stringTokenReplaceWith replacer (token: StringTokens) =
                                let res = replacer (token.GetString())
                                StringResource.stringManager.InternIdentifierToken res

                            let replaceValueWith replacer (v: Value) =
                                match v with
                                | Value.String s -> String(stringTokenReplaceWith replacer s)
                                | Value.QString s -> QString(stringTokenReplaceWith replacer s)
                                | Value.Bool _ | Value.Int _ | Value.Float _ ->
                                    // For non-string values, convert to string, attempt replacement,
                                    // then re-parse if the replacement changed anything.
                                    // This handles cases like script paths containing $PARAM$
                                    // that were parsed as identifiers.
                                    let raw = v.ToRawString()
                                    let replaced = replacer raw
                                    if raw <> replaced then
                                        String(StringResource.stringManager.InternIdentifierToken replaced)
                                    else
                                        v
                                | _ -> v

                            let replaceValue = replaceValueWith stringReplacer

                            node.Leaves
                            |> Seq.iter (fun (l: Leaf) ->
                                l.Key <- stringReplacer l.Key
                                let valueReplacer =
                                    if l.KeyId.lower = keyIdLower || (node.KeyId.lower = keyIdLower && l.KeyId.lower = scriptKeyIdLower) then
                                        inlineScriptPathReplacer
                                    else
                                        stringReplacer
                                l.Value <- replaceValueWith valueReplacer l.Value)

                            // After replacing LeafValues, split any unquoted values that contain spaces
                            // into multiple LeafValues. This handles parameter expansion like
                            // $TAGS$ -> "weapon_type_kinetic weapon_type_energy" which should become
                            // two separate LeafValues, matching how the parser tokenizes unquoted values.
                            let expandedLeafValues =
                                node.AllArray
                                |> Array.collect (fun child ->
                                    match child with
                                    | LeafValueC lv ->
                                        let origValue = lv.Value
                                        let newValue = replaceValue origValue
                                        match origValue with
                                        | Value.QString _ ->
                                            lv.Value <- newValue
                                            [| child |]
                                        | _ ->
                                            let text = newValue.ToRawString()
                                            if text.Contains(" ") then
                                                text.Split([| ' ' |], StringSplitOptions.RemoveEmptyEntries)
                                                |> Array.map (fun part ->
                                                    LeafValueC(LeafValue(String(StringResource.stringManager.InternIdentifierToken(part)), lv.Position)))
                                            else
                                                lv.Value <- newValue
                                                [| child |]
                                    | _ -> [| child |])
                            node.AllArray <- expandedLeafValues

                            node.Nodes |> Seq.iter (foldOverNode stringReplacer inlineScriptPathReplacer)


                        if
                            nodeRefSet.Contains(struct(n.Position.StartLine, n.Position.StartColumn, n.Position.EndLine, n.Position.EndColumn, n.KeyId.lower))
                        then
                            let scriptName = (n.TagText "script")

                            let values =
                                n.Leaves
                                |> Seq.map (fun l ->
                                    let rawValue = l.ValueText
                                    let resolvedValue =
                                        if rawValue.StartsWith("@", StringComparison.Ordinal)
                                           && not (rawValue.StartsWith("@[", StringComparison.Ordinal))
                                           && not (rawValue.StartsWith(@"@\[", StringComparison.Ordinal)) then
                                            match scriptedVariableValues.Value |> Map.tryFind rawValue with
                                            | Some numericValue -> numericValue
                                            | None -> rawValue
                                        else rawValue
                                    "$" + l.Key + "$", resolvedValue)
                                // 只过滤空 key，允许空 value（空值会被替换为空字符串）
                                // 这样 wg_crisis$CURRENT$.100 当 CURRENT 为空时能正确解析为 wg_crisis.100
                                |> Seq.where (fun (k, v) -> k.Length > 0)

                            // Substitute parameters in script name before lookup,
                            // e.g. "rarity_$RARITY$" with RARITY=common -> "rarity_common"
                            match tryFindInlineScript (stringReplace values scriptName) with
                            | Some scriptNode ->
                                let newScriptNode = STLProcess.cloneNode scriptNode
                                foldOverNode (stringReplace values) (stringReplaceWithoutDefaults values) newScriptNode

                                newScriptNode.AllArray
                                |> Seq.map (fun x ->
                                    addTrivia n.Position x
                                    x)
                            // |Some scriptNode -> [CommentC (n.Position, $"Dummy comment to replace empty inline_script {scriptName}")]
                            | _ ->
                                [ LeafValueC(
                                      LeafValue(
                                          Value.String(
                                              stringManager.InternIdentifierToken $"Missing inline_script {scriptName}"
                                          ),
                                          n.Position
                                      )
                                  ) ]
                        else
                            replaceCataFun n
                            [ NodeC n ]
                    | LeafC l ->
                        // log $"b {l.ValueText} {l.Position}"
                        if
                            leafRefSet.Contains(struct(l.Position.StartLine, l.Position.StartColumn, l.Position.EndLine, l.Position.EndColumn, l.KeyId.lower, l.ValueId.lower))
                        then
                            let scriptName = l.ValueText

                            match tryFindInlineScript scriptName with
                            | Some scriptNode ->
                                let newScriptNode = STLProcess.cloneNode scriptNode

                                newScriptNode.AllArray
                                |> Seq.map (fun x ->
                                    addTrivia l.Position x
                                    x)
                            // |Some scriptNode -> [CommentC (l.Position, $"Dummy comment to replace empty inline_script {scriptName}")]
                            | _ ->
                                [ LeafValueC(
                                      LeafValue(
                                          Value.String(
                                              stringManager.InternIdentifierToken $"Missing inline_script {scriptName}"
                                          ),
                                          l.Position
                                      )
                                  ) ]
                        else
                            [ LeafC l ]
                    | x -> [ x ]

                node.AllArray <- node.AllArray |> Seq.collect childFun |> Array.ofSeq

            if List.isEmpty allScriptRefs then
                None
            else
                let newNode = STLProcess.cloneNode e.entity
                replaceCataFun newNode
                Some newNode

        news
        |> Seq.map (function
            | resource, Some struct (oldE, oldLazy) ->
                // 性能优化：跳过 inline_scripts/ 目录内的文件（它们是模板，不需要被展开）
                // 大小写不敏感判断（与 FileManager 的 inline_script 识别、addCallerContributions 一致），
                // 避免 logicalpath 大小写与字面量不一致时模板未被跳过、被当普通文件按规则验证（CW242/CW263 假阳性）
                if oldE.logicalpath.StartsWith(inlinePath, StringComparison.OrdinalIgnoreCase) then
                    resource, Some struct (oldE, oldLazy)
                else

                let maxIter = 5

                let rec updateInner entity i =
                    match i, updateEntity entity with
                    | i, Some newEntity when i = maxIter -> Some newEntity
                    | i, Some newEntity -> updateInner { entity with entity = newEntity } (i + 1)
                    | 0, None -> None
                    | _, None -> Some entity.entity

                let updatedE = updateInner oldE 0

                match updatedE with
                | Some newNode ->
                    let newEntity = { oldE with entity = newNode }

                    let lazyi =
                        System.Lazy<_>((fun () -> computedDataFunction newEntity), LazyThreadSafetyMode.PublicationOnly)

                    let item = struct (newEntity, lazyi)
                    entitiesMap[newEntity.filepath] <- item
                    resource, Some item
                | None -> resource, Some struct (oldE, oldLazy)
            | resource, None -> resource, None)

    let forceRulesData () =
        entitiesMap.Values
        |> PSeq.iter (fun (struct (e, l)) -> computedDataUpdateFunction e (l.Force()))

    let forceRecompute () =
        // 失效 inline_script 缓存，确保下一次展开使用最新数据
        invalidateInlineScriptsCache ()
        for pair in entitiesMap do
            let struct (entity, _) = pair.Value

            let lazyi =
                System.Lazy<_>((fun () -> computedDataFunction entity), LazyThreadSafetyMode.PublicationOnly)

            entitiesMap[pair.Key] <- struct (entity, lazyi)

        // Validation and language features force the data they actually consume.
        // A competing whole-workspace prewarm can evaluate PublicationOnly lazies
        // more than once and amplify peak allocation on large workspaces.
        ResourceManagerEager.nextVersion () |> ignore

    let dynamicParameterPaths =
        [| "common/scripted_effects/"
           "common/scripted_triggers/"
           "common/script_values/"
           "common/inline_scripts/" |]

    let forceDynamicParameterData (timeoutMs: int) (maxEntities: int) =
        let sw = System.Diagnostics.Stopwatch.StartNew()
        let candidates =
            entitiesMap.Values.ToArray()
            |> Array.filter (fun (struct (e, _)) ->
                dynamicParameterPaths
                |> Array.exists (fun p -> e.logicalpath.StartsWith(p, System.StringComparison.Ordinal)))
        let limit =
            if maxEntities <= 0 then candidates.Length else min maxEntities candidates.Length
        let mutable forced = 0
        let mutable i = 0
        while i < limit && (timeoutMs <= 0 || sw.ElapsedMilliseconds < int64 timeoutMs) do
            let struct (_, l) = candidates[i]
            l.Force() |> ignore
            forced <- forced + 1
            i <- i + 1
        forced

    let updateFiles (files: ResourceInput array) =
        let news =
            files |> PSeq.map parseFileThenEntity |> Seq.collect saveResults |> Seq.toList

        updateOverwrite ()
        let mutable res = news

        if enableInlineScripts then
            res <- updateInlineScripts news |> Seq.toList

        rebuildInlineScriptCallerIndex ()

        // Advance the shared version without starting a second full-workspace
        // computation alongside rule setup and initial validation.
        ResourceManagerEager.nextVersion () |> ignore
        res

    /// Parse a single file without changing the live resource maps.
    let prepareFile file =
        let resource, entity = parseFileThenEntity file
        { parsedResource = resource; parsedEntity = entity }

    /// Commit a previously parsed single-file update. The caller serialises this
    /// short mutation phase with other game-state writers.
    let commitPreparedFile (prepared: PreparedResourceUpdate) =
        ResourceManagerEager.nextVersion () |> ignore
        let resource = prepared.parsedResource
        let entity = prepared.parsedEntity

        // Save results to fileMap/entitiesMap, preserving the old overwrite state.
        let savedResults =
            seq {
                match resource with
                | EntityResource(f, _) -> fileMap[f] <- resource
                | FileResource(f, _) -> fileMap[f] <- resource
                | FileWithContentResource(f, _) -> fileMap[f] <- resource

                match entity with
                | Some e ->
                    // 保留旧 Entity 的 overwrite 状态，避免跳过 updateOverwrite 导致状态丢失
                    let preservedOverwrite =
                        match entitiesMap.TryGetValue(e.filepath) with
                        | true, struct (oldE, _) -> oldE.overwrite
                        | _ -> Overwrite.No
                    let e = { e with overwrite = preservedOverwrite }
                    let lazyi =
                        new System.Lazy<_>((fun () -> computedDataFunction e), LazyThreadSafetyMode.PublicationOnly)
                    let item = struct (e, lazyi)
                    entitiesMap[e.filepath] <- item
                    yield resource, Some item
                | None ->
                    let resourcePath =
                        match resource with
                        | EntityResource(f, _) -> f
                        | FileResource(f, _) -> f
                        | FileWithContentResource(f, _) -> f
                    entitiesMap.Remove resourcePath |> ignore
                    removeCallerContributions resourcePath
                    yield resource, None
            } |> Seq.toList

        // Expand inline scripts for this file after it becomes the live resource.
        let mutable res = savedResults
        if enableInlineScripts then
            res <- updateInlineScripts res |> Seq.toList

        // 增量维护 inline_script 反向调用索引（仅本文件的贡献）
        entity |> Option.iter updateInlineScriptCallerIndexForFile

        // 跳过 updateOverwrite — 编辑内容不改变覆盖关系
        // 跳过 forceEagerData — Lazy 值按需求值，避免全量预热导致巨额分配

        if res.Length > 1 then
            log (sprintf "Prepared file %A returned multiple resources" prepared.parsedResource)

        res.[0]

    /// Single-file update used by save/deep-validation paths. Keeping this
    /// wrapper preserves the existing API while editor updates can call the two
    /// phases independently.
    let updateFile file =
        file |> prepareFile |> commitPreparedFile

    let normaliseFilePath (path: string) =
        try
            FileInfo(path).FullName.Replace('\\', '/').ToLowerInvariant()
        with _ ->
            path.Replace('\\', '/').ToLowerInvariant()

    let tryFindStoredFileKey (filepath: string) =
        let target = normaliseFilePath filepath
        fileMap.Keys
        |> Seq.tryFind (fun key -> normaliseFilePath key = target)
        |> Option.orElseWith (fun () ->
            entitiesMap.Keys |> Seq.tryFind (fun key -> normaliseFilePath key = target))

    let refreshInlineScriptCallers (scriptNames: string list) =
        if not enableInlineScripts || List.isEmpty scriptNames then
            []
        else
            invalidateInlineScriptsCache ()

            let callers =
                scriptNames
                |> List.collect getInlineScriptCallers
                |> List.distinctBy normaliseFilePath

            let refreshInputs =
                callers
                |> List.choose (fun caller ->
                    let storedPath = tryFindStoredFileKey caller |> Option.defaultValue caller
                    match fileMap.TryGetValue storedPath, entitiesMap.TryGetValue storedPath with
                    | (true, resource), (true, struct (entity, lazyData)) when not (isInlineScriptEntity entity) ->
                        let rawEntity = { entity with entity = entity.rawEntity }
                        Some(storedPath, resource, Some struct (rawEntity, lazyData))
                    | _ -> None)

            if not (List.isEmpty refreshInputs) then
                refreshInputs
                |> List.map (fun (_, resource, entity) -> resource, entity)
                |> updateInlineScripts
                |> Seq.length
                |> ignore

                // Expanded caller entities were replaced without going through
                // UpdateFile. Advance the shared resource version so scope and
                // language-feature snapshots cannot retain the old node objects.
                ResourceManagerEager.nextVersion () |> ignore

            refreshInputs |> List.map (fun (path, _, _) -> path)

    let removeFile (filepath: string) =
        ResourceManagerEager.nextVersion () |> ignore
        let storedPath = tryFindStoredFileKey filepath |> Option.defaultValue filepath
        let removedResource = fileMap.Remove storedPath
        let removedEntity = entitiesMap.Remove storedPath
        if removedResource || removedEntity then
            invalidateInlineScriptsCache ()
            removeCallerContributions storedPath
            updateOverwrite ()
            if enableInlineScripts then
                rebuildInlineScriptCallerIndex ()
            true
        else
            false

    let getResources () = fileMap.Values |> List.ofSeq

    let validatableFiles () =
        fileMap.Values
        |> List.ofSeq
        |> List.choose (function
            | EntityResource(_, e) -> Some e
            | _ -> None)
        |> List.filter (fun f -> f.validate)

    let allEntities () =
        entitiesMap.Values
        |> Seq.filter (fun struct (e, _) -> e.overwrite <> Overwrite.Overwritten)

    let validatableEntities () =
        entitiesMap.Values
        |> Seq.filter (fun struct (e, _) -> e.overwrite <> Overwrite.Overwritten && e.validate)
        |> Seq.toList

    let getFileNames () : string seq =
        fileMap.Values
        |> Seq.map (function
            | EntityResource(_, r) -> r.logicalpath
            | FileResource(_, r) -> r.logicalpath
            | FileWithContentResource(_, r) -> r.logicalpath)

    let getEntityByFilePath path =
        match entitiesMap.TryGetValue(path) with
        | true, r -> Some r
        | _ -> None

    member _.ManualProcessResource = parseFileThenEntity >> snd
    member _.PrepareFile = prepareFile
    member _.CommitPreparedFile = commitPreparedFile

    member _.ManualProcess (filename: string) (filetext: string) =
        let parsed = CKParser.parseString filetext filename

        match parsed with
        | Failure _ -> None
        | Success(s, _, _) ->
            let filenamenopath = Path.GetFileNameWithoutExtension filename
            Some(shipProcess EntityType.Other filenamenopath (mkZeroFile filename) s)

    member _.Api =
        { new IResourceAPI<'T> with
            member _.UpdateFiles = updateFiles
            member _.UpdateFile = updateFile
            member _.RemoveFile = removeFile
            member _.GetResources = getResources
            member _.ValidatableFiles = validatableFiles
            member _.AllEntities = allEntities
            member _.ValidatableEntities = validatableEntities
            member _.ForceRecompute() = forceRecompute ()
            member _.ForceDynamicParameterData(timeoutMs, maxEntities) =
                forceDynamicParameterData timeoutMs maxEntities
            member _.ForceRulesDataGenerate() = forceRulesData ()
            member _.GetInlineScriptCallers scriptName = getInlineScriptCallers scriptName
            member _.RefreshInlineScriptCallers scriptNames = refreshInlineScriptCallers scriptNames
            member _.GetFileNames = getFileNames
            member _.GetEntityByFilePath path = getEntityByFilePath path }
