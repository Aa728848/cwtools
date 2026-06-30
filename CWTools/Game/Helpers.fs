namespace CWTools.Games

open System
open System.Collections.Generic
open System.IO
open CWTools.Common
open CWTools.Parser
open CWTools.Rules
open CWTools.Utilities
open CWTools.Utilities.Utils

module Helpers =
    let updateEventTargetLinks (embeddedSettings: EmbeddedSettings) =
        let simpleEventTargetLinks =
            embeddedSettings.eventTargetLinks
            |> List.choose (function
                | SimpleLink l -> Some(l :> Effect)
                | _ -> None)

        simpleEventTargetLinks

    let addDataEventTargetLinks (lookup: Lookup) (embeddedSettings: EmbeddedSettings) (addWildCardLinks: bool) =
        // log (sprintf "csr %A" link)
        let types = lookup.typeDefInfo
        let enums = lookup.enumDefs

        let ruleToCompletionListHelper =
            function
            | LeafRule(SpecificField(SpecificValue x), _), _ ->
                seq { yield StringResource.stringManager.GetStringForIDs x }
            | NodeRule(SpecificField(SpecificValue x), _), _ ->
                seq { yield StringResource.stringManager.GetStringForIDs x }
            | LeafRule(NewField.TypeField(TypeType.Simple t), _), _ ->
                types.TryFind(t)
                |> Option.map (fun s -> s |> Seq.map (fun s -> s.id))
                |> Option.defaultValue Seq.empty
            | NodeRule(NewField.TypeField(TypeType.Simple t), _), _ ->
                types.TryFind(t)
                |> Option.map (fun s -> s |> Seq.map (fun s -> s.id))
                |> Option.defaultValue Seq.empty
            | LeafRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _ ->
                types.TryFind(t)
                |> Option.map (fun s -> s |> Seq.map (fun s -> (p + s.id + suff)))
                |> Option.defaultValue Seq.empty
            | NodeRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _ ->
                types.TryFind(t)
                |> Option.map (fun s -> s |> Seq.map (fun s -> (p + s.id + suff)))
                |> Option.defaultValue Seq.empty
            | LeafRule(NewField.ValueField(Enum e), _), _ ->
                enums.TryFind(e)
                |> Option.map (fun (_, s) -> s |> Seq.map (fun (s, _) -> s))
                |> Option.defaultValue Seq.empty
            | NodeRule(NewField.ValueField(Enum e), _), _ ->
                enums.TryFind(e)
                |> Option.map (fun (_, s) -> s |> Seq.map (fun (s, _) -> s))
                |> Option.defaultValue Seq.empty
            | _ -> Seq.empty

        let valuesFromVarDef (lookup: Lookup) name =
            lookup.varDefInfo
            |> Map.tryFind name
            |> Option.map (Array.map (fun (value, _) -> value, None))
            |> Option.defaultValue [||]

        let valuesFromTypeDef (lookup: Lookup) name =
            lookup.typeDefInfo
            |> Map.tryFind name
            |> Option.map (Array.map (fun tdi -> tdi.id, Some(TypeRef(name, tdi.id))))
            |> Option.defaultValue [||]

        let getDataExpressionSetting (expressionName: string) (text: string) =
            RulesParser.getSettingFromString text expressionName

        let convertSourceRuleType (lookup: Lookup) (link: EventTargetDataLink) =
            match link.sourceRuleType.Trim() with
            | x when x.StartsWith '<' && x.EndsWith '>' ->
                let sourceType = x.Trim([| '<'; '>' |])

                match lookup.typeDefInfo |> Map.tryFind sourceType with
                | Some x -> x |> Array.map (fun tdi -> tdi.id, Some(TypeRef(sourceType, tdi.id)))
                | None ->
                    log (sprintf "Link %s refers to undefined type %s" link.name sourceType)
                    [||]
            | x when x.StartsWith "enum[" ->
                let enum = RulesParser.getSettingFromString x "enum"

                match enum |> Option.bind (fun x -> Map.tryFind x lookup.enumDefs) with
                | Some(_, vs) -> (vs |> Array.map (fun (x, _) -> x, None))
                | None ->
                    log (sprintf "Link %s refers to undefined enum %A" link.name enum)
                    [||]
            | x when x.StartsWith "value[" ->
                let valuename = RulesParser.getSettingFromString x "value"

                match valuename |> Option.bind (fun x -> Map.tryFind x lookup.varDefInfo) with
                | Some vs -> vs |> Array.map (fun x -> fst x, None)
                | None ->
                    log (sprintf "Link %s refers to undefined value %A" link.name valuename)
                    [||]
            | x when x.StartsWith "dynamic_value[" ->
                match getDataExpressionSetting "dynamic_value" x with
                | Some valueName ->
                    let values = valuesFromVarDef lookup valueName

                    if values.Length = 0 then
                        log (sprintf "Link %s refers to undefined dynamic value %s" link.name valueName)

                    values
                | None -> [||]
            | "$script_value_reference" ->
                let values =
                    [| yield! valuesFromTypeDef lookup "script_value"
                       yield! valuesFromTypeDef lookup "scripted_value"
                       yield! valuesFromVarDef lookup "script_value"
                       yield! valuesFromVarDef lookup "scripted_value" |]
                    |> Array.distinctBy fst

                if values.Length = 0 then
                    log (sprintf "Link %s refers to undefined script value references" link.name)

                values
            | "$define_reference"
            | "$array_define_reference" -> [||]
            | "$database_object" ->
                lookup.extendedConfigMetadata.databaseObjectTypes
                |> Map.toSeq
                |> Seq.collect (fun (_, config) ->
                    match config.objectType with
                    | Some typeName ->
                        lookup.typeDefInfo
                        |> Map.tryFind typeName
                        |> Option.map (fun values ->
                            values
                            |> Array.map (fun tdi -> config.name + ":" + tdi.id, Some(TypeRef(typeName, tdi.id))))
                        |> Option.defaultValue [||]
                    | None -> [||])
                |> Seq.toArray
            | x when x.StartsWith "$tags[" || x.StartsWith "$tags_condition[" ->
                let expressionName =
                    if x.StartsWith "$tags_condition[" then
                        "$tags_condition"
                    else
                        "$tags"

                match getDataExpressionSetting expressionName x with
                | Some valueName -> valuesFromVarDef lookup valueName
                | None -> [||]
            | x when x.StartsWith "alias_keys_field[" ->
                let aliasKeyMap =
                    let resDict = Dictionary<string, string array>()

                    lookup.configRules
                    |> Seq.choose (function
                        | AliasRule(a, rs) -> Some(a, rs)
                        | _ -> None)
                    |> Seq.groupBy fst
                    |> Seq.iter (fun (k, vs) ->
                        resDict[k] <- vs |> Seq.map snd |> Seq.collect ruleToCompletionListHelper |> Array.ofSeq)

                    resDict

                let aliasname = RulesParser.getSettingFromString x "alias_keys_field"

                match aliasname |> Option.map (fun x -> aliasKeyMap.TryGetValue x) with
                | Some(true, vs) -> vs |> Array.map (fun x -> x, None)
                | Some(false, _)
                | None ->
                    log (sprintf "Link %s refers to undefined alias %A" link.name aliasname)
                    [||]
            | x ->
                log (sprintf "Link %s refers to invalid source %s" link.name x)
                [||]

        let getWildCard (link: EventTargetDataLink) =
            match link.sourceRuleType.Trim(), link.dataPrefix with
            | _, prefix when link.fromArgument ->
                let functionName = prefix |> Option.defaultValue link.name

                Some(
                    ScopedEffect(
                        StringResource.stringManager.InternIdentifierToken(functionName + "("),
                        link.inputScopes,
                        Some link.outputScope,
                        EffectType.Link,
                        link.description,
                        "",
                        true,
                        [],
                        true,
                        false,
                        true,
                        None
                    )
                )
            | x, Some prefix when
                x.StartsWith "value["
                || x.StartsWith "dynamic_value["
                || x = "$script_value_reference"
                || x = "$define_reference"
                || x = "$array_define_reference"
                || x = "$database_object"
                || x.StartsWith "$tags["
                || x.StartsWith "$tags_condition["
                ->
                Some(
                    ScopedEffect(
                        StringResource.stringManager.InternIdentifierToken prefix,
                        link.inputScopes,
                        Some link.outputScope,
                        EffectType.Link,
                        link.description,
                        "",
                        true,
                        [],
                        true,
                        false,
                        true,
                        None
                    )
                )
            | _ -> None

        let links =
            embeddedSettings.eventTargetLinks
            |> Seq.choose (function
                | DataLink l -> Some l
                | _ -> None)

        let convertLinkToEffects (link: EventTargetDataLink) =
            let typeDefinedKeys = convertSourceRuleType lookup link

            let inline keyToEffect (key: string, refHint: ReferenceHint option) =
                let prefkey =
                    if link.fromArgument then
                        let functionName = link.dataPrefix |> Option.defaultValue link.name
                        functionName + "(" + key + ")"
                    else
                        link.dataPrefix
                        |> Option.map (fun pref -> pref + key)
                        |> Option.defaultValue key

                seq {

                    match link.dataLinkType with
                    | DataLinkType.Scope ->
                        yield
                            ScopedEffect(
                                StringResource.stringManager.InternIdentifierToken prefkey,
                                link.inputScopes,
                                Some link.outputScope,
                                EffectType.Link,
                                link.description,
                                "",
                                true,
                                false,
                                refHint
                            )
                    | DataLinkType.Value ->
                        yield
                            ScopedEffect(
                                StringResource.stringManager.InternIdentifierToken prefkey,
                                link.inputScopes,
                                Some link.outputScope,
                                EffectType.ValueTrigger,
                                link.description,
                                "",
                                true,
                                false,
                                refHint
                            )
                    | DataLinkType.Both ->
                        yield
                            ScopedEffect(
                                StringResource.stringManager.InternIdentifierToken prefkey,
                                link.inputScopes,
                                Some link.outputScope,
                                EffectType.Link,
                                link.description,
                                "",
                                true,
                                false,
                                refHint
                            )

                        yield
                            ScopedEffect(
                                StringResource.stringManager.InternIdentifierToken prefkey,
                                link.inputScopes,
                                Some link.outputScope,
                                EffectType.ValueTrigger,
                                link.description,
                                "",
                                true,
                                false,
                                refHint
                            )
                    | _ -> ()
                }

            let all = typeDefinedKeys |> Seq.collect keyToEffect
            let extra = if addWildCardLinks then getWildCard link else None

            seq {
                yield! all

                match extra with
                | Some e -> yield e
                | None -> ()
            }

        let convertArgumentLinkGroupToEffects (links: EventTargetDataLink array) =
            match links with
            | [||] -> Seq.empty
            | _ ->
                let template = links.[0]
                let values = links |> Array.map (convertSourceRuleType lookup)

                let all =
                    if values |> Array.exists Array.isEmpty then
                        Seq.empty
                    else
                        let rec combine index acc =
                            seq {
                                if index >= values.Length then
                                    yield List.rev acc
                                else
                                    for value in values.[index] do
                                        yield! combine (index + 1) (value :: acc)
                            }

                        let separator =
                            match template.argumentSeparator |> Option.map (fun s -> s.Trim().ToLowerInvariant()) with
                            | Some "pipe" -> "|"
                            | _ -> ","

                        let functionName = template.dataPrefix |> Option.defaultValue template.name

                        let inline keyToEffect (args: (string * ReferenceHint option) list) =
                            let key = args |> List.map fst |> String.concat separator

                            let refHint =
                                match args with
                                | [ (_, refHint) ] -> refHint
                                | _ -> None

                            let prefkey = functionName + "(" + key + ")"

                            seq {
                                match template.dataLinkType with
                                | DataLinkType.Scope ->
                                    yield
                                        ScopedEffect(
                                            StringResource.stringManager.InternIdentifierToken prefkey,
                                            template.inputScopes,
                                            Some template.outputScope,
                                            EffectType.Link,
                                            template.description,
                                            "",
                                            true,
                                            false,
                                            refHint
                                        )
                                | DataLinkType.Value ->
                                    yield
                                        ScopedEffect(
                                            StringResource.stringManager.InternIdentifierToken prefkey,
                                            template.inputScopes,
                                            Some template.outputScope,
                                            EffectType.ValueTrigger,
                                            template.description,
                                            "",
                                            true,
                                            false,
                                            refHint
                                        )
                                | DataLinkType.Both ->
                                    yield
                                        ScopedEffect(
                                            StringResource.stringManager.InternIdentifierToken prefkey,
                                            template.inputScopes,
                                            Some template.outputScope,
                                            EffectType.Link,
                                            template.description,
                                            "",
                                            true,
                                            false,
                                            refHint
                                        )

                                    yield
                                        ScopedEffect(
                                            StringResource.stringManager.InternIdentifierToken prefkey,
                                            template.inputScopes,
                                            Some template.outputScope,
                                            EffectType.ValueTrigger,
                                            template.description,
                                            "",
                                            true,
                                            false,
                                            refHint
                                        )
                                | _ -> ()
                            }

                        combine 0 [] |> Seq.collect keyToEffect

                let extra = if addWildCardLinks then getWildCard template else None

                seq {
                    yield! all

                    match extra with
                    | Some e -> yield e
                    | None -> ()
                }

        let regularLinks =
            links
            |> Seq.filter (fun link -> not link.fromArgument)
            |> Seq.collect convertLinkToEffects

        let argumentLinks =
            links
            |> Seq.filter _.fromArgument
            |> Seq.groupBy (fun link ->
                link.name,
                link.inputScopes,
                link.outputScope,
                link.description,
                link.dataPrefix,
                link.argumentSeparator,
                link.forDefinitionType,
                link.dataLinkType)
            |> Seq.collect (fun (_, groupedLinks) -> groupedLinks |> Seq.toArray |> convertArgumentLinkGroupToEffects)

        Seq.append regularLinks argumentLinks |> Seq.cast<Effect> |> List.ofSeq

    let getLocalisationErrors (game: GameObject<_, _>) globalLocalisation =
        fun (force: bool, forceGlobal: bool) ->
            let resources = game.Resources
            // Cache ValidatableEntities for this call — avoids double materialization
            let validatableEntities = resources.ValidatableEntities()

            let rulesLocErrors =
                let locKeysArray = game.LocalisationManager.LocalisationKeys()
                game.ValidationManager.CachedRuleErrors(validatableEntities)
                |> List.filter (fun e ->
                    if e.code = "CW100" then
                        match e.data with
                        | Some key ->
                            let exists = locKeysArray |> Array.exists (fun (_, keys) -> keys.Contains key)
                            not exists
                        | None -> true
                    else
                        false)

            let genGlobal () =
                let ges = globalLocalisation (game)
                game.LocalisationManager.globalLocalisationErrors <- Some ges
                ges

            let genAll () =
                let les =
                    (game.ValidationManager.ValidateLocalisation(validatableEntities))

                game.LocalisationManager.localisationErrors <- Some les
                les

            rulesLocErrors
            @ match game.LocalisationManager.localisationErrors, game.LocalisationManager.globalLocalisationErrors with
              | Some les, Some ges -> (if force then genAll () else les) @ (if forceGlobal then genGlobal () else ges)
              | None, Some ges -> genAll () @ (if forceGlobal then genGlobal () else ges)
              | Some les, None -> (if force then genAll () else les) @ genGlobal ()
              | None, None -> genAll () @ genGlobal ()

    let createTypeDefInfo validate id range explicitLocalisation subtypes =
        { TypeDefInfo.id = id
          validate = validate
          range = range
          explicitLocalisation = explicitLocalisation
          subtypes = subtypes }

    open CWTools.Process.Localisation.ChangeLocScope
    open CWTools.Validation.LocalisationString
    open CWTools.Process.Scopes.Scopes
    open CWTools.Process.Localisation
    open CWTools.Validation

    // let hardcodedLocalisation = [ "playername"; "prov" ]
    let hardcodedLocalisation = []

    let validateProcessedLocalisation
        (scriptedVarNames: Set<string>)
        : ((Lang * LocKeySet) array -> (Lang * Map<string, LocEntry>) list -> ValidationResult) =
        validateProcessedLocalisationBase hardcodedLocalisation scriptedVarNames

    let createJominiLocalisationFunctions
        (jominiLocDataTypes: CWTools.Parser.DataTypeParser.JominiLocDataTypes option)
        =
        fun (lookup: Lookup) ->
            let dataTypes =
                jominiLocDataTypes
                |> Option.defaultValue
                    { promotes = Map.empty
                      confidentFunctions = Map.empty
                      functions = Map.empty
                      dataTypes = Map.empty
                      dataTypeNames = Set.empty }

            let localisationCommandValidator =
                createJominiLocalisationCommandValidator dataTypes

            let validateLocalisationCommand =
                validateJominiLocalisationCommandsBase localisationCommandValidator

            let localisationCommandValidatorDefaultContext =
                localisationCommandValidator defaultContext

            let processLocalisation =
                processJominiLocalisationBase localisationCommandValidatorDefaultContext

            let definedEventTargets =
                (lookup.varDefInfo.TryFind "event_target"
                 |> Option.defaultValue [||]
                 |> Array.map fst)

            let eventtargets =
                lookup.savedEventTargets
                |> Seq.map (fun (a, _, c) -> (a, c))
                |> Seq.distinct
                |> List.ofSeq
                |> List.fold
                    (fun map (k, s) ->
                        if Map.containsKey k map then
                            Map.add k (s :: map.[k]) map
                        else
                            Map.add k [ s ] map)
                    Map.empty

            let eventtargets =
                definedEventTargets
                |> Array.fold (fun oldMap et -> oldMap |> Map.add et [ scopeManager.AnyScope ]) eventtargets

            processLocalisation eventtargets, validateLocalisationCommand eventtargets


    let createLocalisationFunctions
        locStaticSettings
        createLocDynamicSettings
        (commands, variableCommands, localisationLinks)
        =
        fun (lookup: Lookup) ->
            let localisationCommandValidator commands variableCommands =
                createLegacyLocalisationCommandValidator (locStaticSettings commands variableCommands localisationLinks)

            let processLocalisation =
                fun commands variableCommands dynamicSettings ->
                    processLocalisationBase
                        (localisationCommandValidator commands variableCommands dynamicSettings)
                        defaultContext

            let validateLocalisationCommand =
                fun commands variableCommands dynamicSettings ->
                    validateLocalisationCommandsBase (
                        localisationCommandValidator commands variableCommands dynamicSettings
                    )

            processLocalisation commands variableCommands (createLocDynamicSettings (lookup)),
            validateLocalisationCommand commands variableCommands (createLocDynamicSettings (lookup))

    let initializeScopesAndModifierCategories configs defaultScopeInputs defaultModifiersInputs =
        configs
        |> List.tryFind (fun (fileName: string, _) ->
            Path.GetFileName(fileName.AsSpan()).Equals("scopes.cwt", StringComparison.OrdinalIgnoreCase))
        |> (fun f -> UtilityParser.initializeScopes f (Some(defaultScopeInputs ())))

        configs
        |> List.tryFind (fun (fileName, _) ->
            Path.GetFileName(fileName.AsSpan()).Equals("modifier_categories.cwt", StringComparison.OrdinalIgnoreCase))
        |> (fun f -> UtilityParser.initializeModifierCategories f (Some(defaultModifiersInputs ())))

    let getActualModifiers configs =
        configs
        |> List.tryFind (fun (fileName: string, _) -> Path.GetFileName fileName = "modifiers.cwt")
        |> Option.map (fun (fileName, fileText) -> UtilityParser.loadModifiers fileName fileText)
        |> Option.defaultValue [||]

    let getFeatureSettings configs =
        configs
        |> List.tryFind (fun (fileName: string, _) -> Path.GetFileName fileName = "settings.cwt")
        |> Option.bind (fun (fileName, fileText) -> UtilityParser.loadSettingsFile fileName fileText)
        |> Option.defaultValue UtilityParser.FeatureSettings.Default
