namespace CWTools.Games.Stellaris

open System
open System.Collections.Generic
open System.Diagnostics
open CWTools.Game
open CWTools.Parser
open CWTools.Process
open CWTools.Utilities.Position
open CWTools.Utilities.Utils2
open CWTools.Validation.Stellaris.STLValidation
open CWTools.Validation
open CWTools.Validation.ValidationCore
open CWTools.Localisation
open CWTools.Localisation.STL
open CWTools.Common
open CWTools.Common.STLConstants
open CWTools.Process.Scopes.STL
open CWTools.Validation.Stellaris.STLLocalisationValidation
open CWTools.Validation.Stellaris.STLEventValidation
open CWTools.Validation.Stellaris.STLLocalisationString
open CWTools.Utilities
open CWTools.Validation.Stellaris.Graphics
open CWTools.Games
open CWTools.Games.Stellaris
open CWTools.Rules
open CWTools.Validation.Common.CommonValidation
open CWTools.Process.Scopes
open CWTools.Process.Scopes.Scopes
open System.Text
open CWTools.Games.LanguageFeatures
open CWTools.Validation.LocalisationString
open CWTools.Games.Helpers
open System.IO
open CWTools.Process.Localisation
open System.Linq
open System.Collections.Generic

module STLGameFunctions =
    type GameObject = GameObject<STLComputedData, STLLookup>

    let createLocDynamicSettings (lookup: Lookup) =
        let definedEventTargets =
            Array.append
                (lookup.varDefInfo.TryFind "event_target"
                 |> Option.defaultValue [||]
                 |> Array.map fst)
                (lookup.varDefInfo.TryFind "global_event_target"
                 |> Option.defaultValue [||]
                 |> Array.map fst)

        let savedEventTargets =
            lookup.savedEventTargets
            |> Seq.map (fun (name, _, scope) -> name, scope)

        let eventTargets =
            Seq.append
                (definedEventTargets |> Seq.map (fun name -> name, scopeManager.AnyScope))
                savedEventTargets
            |> Seq.distinct
            |> Array.ofSeq

        let definedVariables =
            (lookup.varDefInfo.TryFind "variable"
             |> Option.defaultValue [||]
             |> Seq.map fst
             |> IgnoreCaseStringSet)

        { scriptedLocCommands = lookup.scriptedLoc |> Array.map (fun s -> s, [ scopeManager.AnyScope ])
          eventTargets = eventTargets
          setVariables = definedVariables }

    /// Build exact links only for saved event-target names that have one
    /// unambiguous scope across the loaded project. Ambiguous names deliberately
    /// keep the legacy Any fallback until context-sensitive propagation can
    /// distinguish their call paths.
    let savedEventTargetLinks (lookup: Lookup) =
        lookup.savedEventTargets
        |> Seq.filter (fun (name, _, _) ->
            not (String.IsNullOrWhiteSpace name)
            && not (name.Contains '$'))
        |> Seq.groupBy (fun (name, _, _) -> name.ToLowerInvariant())
        |> Seq.choose (fun (_, targets) ->
            let targets = targets |> Seq.toArray
            let scopes = targets |> Array.map (fun (_, _, scope) -> scope) |> Array.distinct

            match targets, scopes with
            | [||], _ -> None
            | _, [| scope |] when not (scope.Equals scopeManager.AnyScope) ->
                let name, _, _ = targets[0]

                Some(
                    ScopedEffect(
                        "event_target:" + name,
                        scopeManager.AllScopes,
                        scope,
                        EffectType.Link,
                        "Saved event target",
                        "",
                        true
                    )
                    :> Effect
                )
            | _ -> None)
        |> List.ofSeq

    let updateScriptedTriggers (game: GameObject) =
        let vanillaTriggers =
            let se = game.Lookup.triggers
            let vt = game.Settings.embedded.triggers |> List.map (fun e -> e :> Effect)
            se @ vt

        let sts, ts = STLLookup.updateScriptedTriggers game.Resources vanillaTriggers
        game.Lookup.onlyScriptedTriggers <- sts
        sts @ ts

    let updateScriptedEffects (game: GameObject) =
        let vanillaEffects =
            let se = game.Lookup.effects
            let ve = game.Settings.embedded.effects |> List.map (fun e -> e :> Effect)
            se @ ve

        let ses, es =
            STLLookup.updateScriptedEffects game.Resources vanillaEffects game.Lookup.triggers

        game.Lookup.onlyScriptedEffects <- ses
        ses @ es

    let updateStaticodifiers (game: GameObject) =
        let rawModifiers =
            game.Resources.AllEntities()
            |> Seq.choose (function
                | struct (f, _) when f.filepath.Contains("static_modifiers") -> Some f.entity
                | _ -> None)
            |> Seq.collect _.Nodes
            |> Seq.toArray

        let modifiers2 =
            Enumerable.ToLookup(game.Settings.embedded.modifiers, (fun x -> x.tag), (fun x -> x.category))

        let newModifiers =
            rawModifiers |> Array.map (STLProcess.getStaticModifierCategory modifiers2)

        game.Lookup.staticModifiers <- newModifiers

    let updateScriptedLoc (game: GameObject) =
        let rawLocs =
            game.Resources.AllEntities()
            |> Seq.choose (function
                | struct (f, _) when f.filepath.Contains("scripted_loc") -> Some f.entity
                | _ -> None)
            |> Seq.collect (fun n -> n.Nodes)
            |> Seq.map (fun l -> l.TagText "name")
            |> Array.ofSeq

        game.Lookup.embeddedScriptedLoc <-
            game.Settings.embedded.cachedRuleMetadata
            |> Option.map _.scriptedLoc
            |> Option.defaultValue [||]

        game.Lookup.scriptedLoc <- rawLocs

    let scriptedTypeKeyForPath (filepath: string) =
        let path = filepath.Replace('\\', '/').ToLowerInvariant()
        if path.Contains("common/scripted_triggers/") then Some "scripted_trigger"
        elif path.Contains("common/scripted_effects/") then Some "scripted_effect"
        elif path.Contains("common/script_values/") then Some "script_value"
        else None

    let normaliseRefreshPath (filepath: string) =
        filepath.Replace('\\', '/').ToLowerInvariant()

    let private effectSemanticSignature prefix (effect: Effect) =
        let scopes =
            effect.Scopes
            |> List.map (fun scope -> string scope.Tag)
            |> String.concat ","

        let details =
            match effect with
            | :? ScriptedEffect as scripted ->
                let targets =
                    [ scripted.GlobalEventTargets
                      scripted.SavedEventTargets
                      scripted.UsedEventTargets
                      scripted.FiredOnActions ]
                    |> List.map (List.sort >> String.concat ",")
                    |> String.concat "|"
                scripted.Comments + "|" + targets
            | :? DocEffect as doc ->
                let target =
                    doc.Target
                    |> Option.map (fun value -> string value.Tag)
                    |> Option.defaultValue ""
                String.concat "|" [ doc.Desc; doc.Usage; target ]
            | _ -> ""

        $"{prefix}|{effect.Name.GetString()}|{int effect.Type}|{scopes}|{details}"

    /// File contribution used by the LSP to decide whether a scripted edit can
    /// take the range-only type-index path. It deliberately includes inferred
    /// scopes/targets and per-file dynamic parameters, but excludes source ranges.
    let semanticSignatureForFile (game: GameObject) filepath =
        match game.Resources.GetEntityByFilePath filepath, game.InfoService with
        | Some struct (entity, computed), Some infoService ->
            let path = normaliseRefreshPath filepath
            let localSignature = infoService.GetSemanticSignature entity

            let parameterSignature =
                if path.Contains("/common/scripted_effects/")
                   || path.Contains("/common/scripted_triggers/") then
                    computed.Force().ScriptedEffectParams
                    |> Option.defaultWith (fun () -> Compute.EU4.getScriptedEffectParamsEntity entity)
                    |> List.distinct
                    |> List.sort
                    |> List.map (fun parameter -> "parameter|effect|" + parameter)
                    |> List.toArray
                elif path.Contains("/common/script_values/") then
                    computed.Force().ScriptValueParams
                    |> Option.defaultWith (fun () -> Compute.Jomini.getScriptValueParamsEntity entity)
                    |> List.distinct
                    |> List.sort
                    |> List.map (fun parameter -> "parameter|value|" + parameter)
                    |> List.toArray
                else
                    [||]

            let definitionSignature =
                if path.Contains("/common/scripted_effects/") then
                    game.Lookup.onlyScriptedEffects
                    |> List.map (effectSemanticSignature "effect")
                    |> List.sort
                    |> List.toArray
                elif path.Contains("/common/scripted_triggers/") then
                    game.Lookup.onlyScriptedTriggers
                    |> List.map (effectSemanticSignature "trigger")
                    |> List.sort
                    |> List.toArray
                else
                    [||]

            Array.concat [ localSignature; parameterSignature; definitionSignature ]
            |> Array.sort
            |> Some
        | _ -> None

    let isInlineScriptRefreshPath (filepath: string) =
        normaliseRefreshPath filepath
        |> fun path -> path.Contains("/common/inline_scripts/")

    let incrementalTypeKeysForFiles (game: GameObject<STLComputedData, STLLookup>) files =
        let files = files |> List.filter (isInlineScriptRefreshPath >> not)
        let fileSet = files |> List.map normaliseRefreshPath |> Set.ofList
        let indexedTypeKeys =
            game.Lookup.typeDefInfo
            |> Map.toSeq
            |> Seq.choose (fun (typeKey, infos) ->
                if infos |> Array.exists (fun info -> fileSet.Contains(normaliseRefreshPath info.range.FileName)) then
                    Some typeKey
                else
                    None)
            |> Seq.toList

        let currentTypeKeys =
            files
            |> Seq.choose (fun filepath -> game.Resources.GetEntityByFilePath filepath)
            |> Seq.collect (fun struct (entity, _) ->
                game.Lookup.typeDefs
                |> Seq.choose (fun definition ->
                    if CSharpHelpers.FieldValidatorsHelper.CheckPathDir(definition.pathOptions, entity.logicalpath) then
                        Some definition.name
                    else
                        None))
            |> Seq.toList

        (indexedTypeKeys @ currentTypeKeys @ (files |> List.choose scriptedTypeKeyForPath))
        |> List.distinct

    let globalLocalisation (game: GameObject) =
        let locfiles =
            game.Resources.GetResources()
            |> List.choose (function
                | FileWithContentResource(_, e) -> Some e
                | _ -> None)
            |> List.filter (fun f ->
                f.overwrite <> Overwrite.Overwritten
                && Path.GetExtension(f.filepath.AsSpan()).Equals(".yml", StringComparison.OrdinalIgnoreCase)
                && f.validate)
            |> List.map _.filepath

        let locFileValidation = validateLocalisationFiles locfiles

        let locParseErrors =
            game.LocalisationManager.GetLocalisationAPIs()
            <&!&> (fun struct (b, api) -> if b then validateLocalisationSyntax api.Results else OK)

        let globalTypeLoc = game.ValidationManager.ValidateGlobalLocalisation()

        game.Lookup.proccessedLoc
        |> validateProcessedLocalisation
            (game.Lookup.scriptedVariables |> List.map fst |> Set.ofList)
            game.LocalisationManager.taggedLocalisationKeys
        <&&> locFileValidation
        <&&> globalTypeLoc
        <&&> locParseErrors
        |> (function
        | Invalid(_, es) -> es
        | _ -> [])

    let validateIncrementalLocalisationFiles
        (game: GameObject)
        (changedKeys: string array)
        (initialFiles: seq<string>)
        =
        let pathComparer = if OperatingSystem.IsWindows() then StringComparer.OrdinalIgnoreCase else StringComparer.Ordinal
        let affectedFiles = HashSet<string>(pathComparer)
        affectedFiles.UnionWith initialFiles
        if changedKeys.Length > 0 then
            affectedFiles.UnionWith(game.ValidationManager.LocalisationFilesForKeys changedKeys)
            affectedFiles.UnionWith(game.ValidationManager.GlobalLocalisationFilesForKeys changedKeys)
        let affectedFileSet = affectedFiles |> Set.ofSeq

        let localisationFiles =
            affectedFiles
            |> Seq.filter (fun filepath ->
                Path.GetExtension(filepath.AsSpan()).Equals(".yml", StringComparison.OrdinalIgnoreCase))
            |> Seq.toList

        let locFileValidation = validateLocalisationFiles localisationFiles
        let locParseErrors =
            game.LocalisationManager.GetLocalisationAPIsForFiles affectedFileSet
            <&!&> (fun struct (validate, api) -> if validate then validateLocalisationSyntax api.Results else OK)

        let processedErrors =
            game.LocalisationManager.ProcessedLocalisationForFiles affectedFileSet
            |> validateProcessedLocalisation
                (game.Lookup.scriptedVariables |> List.map fst |> Set.ofList)
                game.LocalisationManager.taggedLocalisationKeys

        let globalTypeErrors =
            game.ValidationManager.ValidateGlobalLocalisationForFiles affectedFileSet

        let onlyAffected errors = errors |> List.filter (fun error -> affectedFileSet.Contains error.range.FileName)
        let localErrors = game.ValidationManager.ValidateLocalisationFiles affectedFileSet |> onlyAffected
        let cachedRuleErrors =
            game.ValidationManager.CachedRuleLocalisationErrorsForFiles affectedFileSet
            |> onlyAffected
        let globalErrors =
            processedErrors
            <&&> locFileValidation
            <&&> locParseErrors
            <&&> globalTypeErrors
            |> function
                | Invalid(_, errors) -> errors |> onlyAffected
                | _ -> []

        game.LocalisationManager.ApplyIncrementalErrors(affectedFileSet, localErrors, globalErrors)
        { affectedFiles = affectedFiles |> Seq.toArray
          errors = cachedRuleErrors @ localErrors @ globalErrors }

    let validateIncrementalLocalisation (game: GameObject) (delta: LocalisationDelta) =
        validateIncrementalLocalisationFiles game delta.changedKeys delta.affectedLocalisationFiles

    let addModifiersFromCoreAndTypes
        (lookup: Lookup)
        (embeddedSettings: EmbeddedSettings)
        (resources: IResourceAPI<_>)
        =
        let typeGeneratedModifiers =
            RulesHelpers.generateModifiersFromTypes lookup.typeDefs lookup.typeDefInfo

        // When everything is changed to arrays later, this code needs to be updated accordingly.
        Debug.Assert(lookup.typeDefs.GetType() = typeof<list<TypeDefinition>>)
        let current = (embeddedSettings.modifiers |> List.ofArray) @ typeGeneratedModifiers

        lookup.coreModifiers <-
            addGeneratedModifiers current (EntitySet(resources.AllEntities()))
            |> List.toArray

    // let updateModifiers(game : GameObject) =
    // game.Lookup.coreModifiers <- addGeneratedModifiers game.Settings.embedded.modifiers (EntitySet (game.Resources.AllEntities()))

    let updateTechnologies (game: GameObject) =
        game.Lookup.technologies <- getTechnologies (EntitySet(game.Resources.AllEntities()))

    let addModifiersWithScopes (lookup: Lookup) : RootRule array =
        let modifierOptions (modifier: ActualModifier) =
            let requiredScopes = modifierCategoryManager.SupportedScopes modifier.category

            { Options.DefaultOptions with
                requiredScopes = requiredScopes }

        let processField =
            RulesParser.processTagAsField (scopeManager.ParseScope()) scopeManager.AnyScope scopeManager.ScopeGroups

        (lookup.coreModifiers
         |> Seq.map (fun c ->
             AliasRule(
                 "modifier",
                  NewRule(LeafRule(processField c.tag, ValueField(ValueType.Float(RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum))), modifierOptions c)
             )))
            .Concat(RulesHelpers.generateModifierRulesFromTypes lookup.typeDefs)
            .ToArray()

    /// Carrier is a planet-or-ship union. A contract supported by either
    /// possible host is valid for the synthetic Carrier scope.
    let internal normalizeCarrierScopeSet planetScope shipScope carrierScope (scopes: Scope list) =
        let withoutCarrier = scopes |> List.filter (fun scope -> not (scope.Equals carrierScope))
        let supports scope = withoutCarrier |> List.exists (fun candidate -> candidate.Equals scope)

        if supports planetScope || supports shipScope then
            withoutCarrier @ [ carrierScope ]
        else
            withoutCarrier

    let private normalizeCarrierScopes (scopes: Scope list) =
        let tryScopeByName name =
            scopeManager.AllScopes
            |> List.tryFind (fun scope ->
                String.Equals(scopeManager.GetName scope, name, StringComparison.OrdinalIgnoreCase))

        match tryScopeByName "Planet", tryScopeByName "Ship", tryScopeByName "Carrier" with
        | Some planetScope, Some shipScope, Some carrierScope ->
            normalizeCarrierScopeSet planetScope shipScope carrierScope scopes
        | _ -> scopes

    let private normalizeCarrierEffect (effect: Effect) =
        let scopes = normalizeCarrierScopes effect.Scopes

        match effect with
        | :? ScopedEffect as scoped ->
            ScopedEffect(
                scoped.Name,
                scopes,
                scoped.Target,
                scoped.Type,
                scoped.Desc,
                scoped.Usage,
                scoped.IsScopeChange,
                scoped.IgnoreChildren,
                scoped.ScopeOnlyNotEffect,
                scoped.IsValueScope,
                scoped.IsWildCard,
                scoped.RefHint
            )
            :> Effect
        | :? DocEffect as documented ->
            DocEffect(
                documented.Name,
                scopes,
                documented.Target,
                documented.Type,
                documented.Desc,
                documented.Usage,
                documented.RefHint
            )
            :> Effect
        | :? ScriptedEffect as scripted ->
            ScriptedEffect(
                scripted.Name,
                scopes,
                scripted.Type,
                scripted.Comments,
                scripted.GlobalEventTargets,
                scripted.SavedEventTargets,
                scripted.UsedEventTargets,
                scripted.FiredOnActions
            )
            :> Effect
        | basic -> Effect(basic.Name, scopes, basic.Type, basic.RefHint)

    let private setCarrierAwareCoreLinks (lookup: Lookup) links =
        lookup.allCoreLinks <- links |> List.map normalizeCarrierEffect

    let addTriggerDocsScopes (lookup: Lookup) (rules: RootRule array) =
        let scriptedOptions (scripted: string) (effect: ScriptedEffect) =
            { Options.DefaultOptions with
                description = Some effect.Comments
                requiredScopes = normalizeCarrierScopes effect.Scopes
                typeHint = Some(scripted, true) }

        let scriptedValueTriggerOptions (scripted: string) (effect: ScriptedEffect) =
            { scriptedOptions scripted effect with
                comparison = true }

        let intValueField =
            ValueScopeField(
                true,
                (decimal RulesParserConstants.IntFieldDefaultMinimum,
                 decimal RulesParserConstants.IntFieldDefaultMaximum)
            )

        let getAllScriptedEffects =
            lookup.onlyScriptedEffects
            |> Seq.choose (function
                | :? ScriptedEffect as se -> Some se
                | _ -> None)
            |> Seq.map (fun se ->
                AliasRule(
                    "effect",
                    NewRule(
                        LeafRule(CWTools.Rules.RulesParser.specificFieldFromId se.Name, ValueField(ValueType.Bool)),
                        scriptedOptions "scripted_effect" se
                    )
                ))
            |> Seq.toArray

        let getAllScriptedTriggers =
            lookup.onlyScriptedTriggers
            |> Seq.choose (function
                | :? ScriptedEffect as se -> Some se
                | _ -> None)
            |> Seq.collect (fun se ->
                let field = RulesParser.specificFieldFromId se.Name

                if se.Type = EffectType.ValueTrigger then
                    let options = scriptedValueTriggerOptions "scripted_trigger" se

                    [| AliasRule("trigger", NewRule(LeafRule(field, intValueField), options))
                       AliasRule("trigger", NewRule(LeafRule(field, ScopeField options.requiredScopes), options)) |]
                else
                    [| AliasRule(
                           "trigger",
                           NewRule(
                               LeafRule(field, ValueField(ValueType.Bool)),
                               scriptedOptions "scripted_trigger" se
                           )
                       ) |])
            |> Seq.toArray

        let addRequiredScopesE (s: StringTokens) (o: Options) =
            let newScopes =
                match o.requiredScopes with
                | [] ->
                    lookup.effectsMap.TryFind(StringResource.stringManager.GetStringForID s.normal)
                    |> Option.map (fun se -> se.Scopes)
                    |> Option.defaultValue []
                | x -> x

            { o with requiredScopes = normalizeCarrierScopes newScopes }

        let addRequiredScopesT (s: StringTokens) (o: Options) =
            let newScopes =
                match o.requiredScopes with
                | [] ->
                    lookup.triggersMap.TryFind(StringResource.stringManager.GetStringForID s.normal)
                    |> Option.map (fun se -> se.Scopes)
                    |> Option.defaultValue []
                | x -> x

            { o with requiredScopes = normalizeCarrierScopes newScopes }

        rules
        |> Array.collect (function
            | AliasRule("effect", (LeafRule(SpecificField(SpecificValue s), r), o)) ->
                [| AliasRule("effect", (LeafRule(SpecificField(SpecificValue s), r), addRequiredScopesE s o)) |]
            | AliasRule("trigger", (LeafRule(SpecificField(SpecificValue s), r), o)) ->
                [| AliasRule("trigger", (LeafRule(SpecificField(SpecificValue s), r), addRequiredScopesT s o)) |]
            | AliasRule("effect", (NodeRule(SpecificField(SpecificValue s), r), o)) ->
                [| AliasRule("effect", (NodeRule(SpecificField(SpecificValue s), r), addRequiredScopesE s o)) |]
            | AliasRule("trigger", (NodeRule(SpecificField(SpecificValue s), r), o)) ->
                [| AliasRule("trigger", (NodeRule(SpecificField(SpecificValue s), r), addRequiredScopesT s o)) |]
            | AliasRule("effect", (LeafValueRule(SpecificField(SpecificValue s)), o)) ->
                [| AliasRule("effect", (LeafValueRule(SpecificField(SpecificValue s)), addRequiredScopesE s o)) |]
            | AliasRule("trigger", (LeafValueRule(SpecificField(SpecificValue s)), o)) ->
                [| AliasRule("trigger", (LeafValueRule(SpecificField(SpecificValue s)), addRequiredScopesT s o)) |]
            | AliasRule("effect", (LeafRule(TypeField(TypeType.Simple "scripted_effect"), o), _)) ->
                getAllScriptedEffects
            | AliasRule("trigger", (LeafRule(TypeField(TypeType.Simple "scripted_trigger"), o), _)) ->
                getAllScriptedTriggers
            | x -> [| x |])

    let addValueTriggersToTriggers rules (lookup: Lookup) =
        let triggers =
            rules
            |> Seq.choose (function
                | AliasRule("trigger", (LeafRule(SpecificField(SpecificValue n), _), o)) ->
                    Some(StringResource.stringManager.GetStringForID n.normal, o)
                | _ -> None)
            |> Map.ofSeq

        let inline triggerAugment (trigger: Effect) =
            match trigger, triggers |> Map.tryFind (trigger.Name.GetString()) with
            | :? DocEffect as doc, Some options when options.comparison ->
                [ DocEffect(
                      "trigger:" + doc.Name.GetString(),
                      doc.Scopes,
                      doc.Target,
                      EffectType.ValueTrigger,
                      doc.Desc,
                      doc.Usage,
                      doc.RefHint
                  )
                  :> Effect
                  doc :> Effect ]
            | trigger, _ -> [ trigger ]

        lookup.triggers |> List.collect triggerAugment
    //        lookup.triggers |> List.

    let loadConfigRulesHook (rules: RootRule array) (lookup: Lookup) embedded =
        let triggersWithValueTriggers = addValueTriggersToTriggers rules lookup
        setCarrierAwareCoreLinks
            lookup
            (triggersWithValueTriggers @ lookup.effects @ updateEventTargetLinks embedded) //@ addDataEventTargetLinks lookup embedded
        lookup.coreModifiers <- embedded.modifiers
        let rulesWithMod = rules.Concat(addModifiersWithScopes (lookup)).ToArray()
        let rulesWithEmbeddedScopes = addTriggerDocsScopes lookup rulesWithMod
        rulesWithEmbeddedScopes



    let addModifiersAsTypes (lookup: Lookup) (typesMap: Map<string, TypeDefInfo array>) =
        typesMap.Add(
            "modifier",
            lookup.coreModifiers
            |> Array.map (fun m -> createTypeDefInfo false m.tag range.Zero [] [])
        )

    let private planetKillerOnActionNames (resources: IResourceAPI<_>) =
        let seen = System.Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)

        let addIfNew name pos =
            if seen.Add name then Some(name, pos) else None

        EntitySet(resources.AllEntities()).AllOfTypeChildren EntityType.ComponentTemplates
        |> Seq.filter (fun ct -> String.Equals(ct.TagText "type", "planet_killer", StringComparison.OrdinalIgnoreCase))
        |> Seq.collect (fun ct ->
            let key = ct.TagText "key"

            if String.IsNullOrWhiteSpace key then
                Seq.empty
            else
                let baseName = "on_destroy_planet_with_" + key

                seq {
                    yield baseName, ct.Position
                    yield baseName + "_queued", ct.Position
                    yield baseName + "_unqueued", ct.Position
                })
        |> Seq.choose (fun (name, pos) -> addIfNew name pos)
        |> Array.ofSeq

    let private addDynamicPlanetKillerOnActions (lookup: Lookup) (resources: IResourceAPI<_>) =
        if lookup.typeDefs |> List.exists (fun td -> String.Equals(td.name, "on_action", StringComparison.OrdinalIgnoreCase)) then
            let generated = planetKillerOnActionNames resources
            let generatedIds = generated |> Array.map fst

            let isGeneratedPlanetKillerTypeDef (tdi: TypeDefInfo) =
                not tdi.validate
                && tdi.subtypes = [ "dynamic_planet_killer" ]
                && tdi.id.StartsWith("on_destroy_planet_with_", StringComparison.OrdinalIgnoreCase)

            let existingOnActions =
                lookup.typeDefInfo
                |> Map.tryFind "on_action"
                |> Option.defaultValue [||]
                |> Array.filter (isGeneratedPlanetKillerTypeDef >> not)

            let existingIds =
                System.Collections.Generic.HashSet<string>(
                    existingOnActions |> Seq.map (fun tdi -> tdi.id),
                    StringComparer.OrdinalIgnoreCase
                )

            let generatedTypeDefs =
                generated
                |> Array.choose (fun (id, pos) ->
                    if existingIds.Add id then
                        Some(createTypeDefInfo false id pos [] [ "dynamic_planet_killer" ])
                    else
                        None)

            lookup.typeDefInfo <-
                lookup.typeDefInfo
                |> Map.add "on_action" (Array.append existingOnActions generatedTypeDefs)

            lookup.typeDefs <-
                lookup.typeDefs
                |> List.map (fun td ->
                    if String.Equals(td.name, "on_action", StringComparison.OrdinalIgnoreCase) then
                        let preservedSubtypes =
                            td.subtypes
                            |> List.filter (fun st ->
                                not (
                                    String.Equals(st.name, "dynamic_planet_killer", StringComparison.OrdinalIgnoreCase)
                                    && st.typeKeyField.IsSome
                                ))

                        let template =
                            td.subtypes
                            |> List.tryFind (fun st ->
                                String.Equals(st.name, "dynamic_planet_killer", StringComparison.OrdinalIgnoreCase)
                                && st.startsWith.IsSome)

                        match template with
                        | Some template ->
                            let existingSubtypeKeys =
                                System.Collections.Generic.HashSet<string>(
                                    preservedSubtypes |> Seq.choose (fun st -> st.typeKeyField),
                                    StringComparer.OrdinalIgnoreCase
                                )

                            let generatedSubtypes =
                                generatedIds
                                |> Array.choose (fun id ->
                                    if existingSubtypeKeys.Add id then
                                        Some(
                                            { template with
                                                typeKeyField = Some id
                                                startsWith = None }
                                        )
                                    else
                                        None)
                                |> Array.toList

                            { td with subtypes = preservedSubtypes @ generatedSubtypes }
                        | None -> td
                    else
                        td)

    let refreshConfigAfterFirstTypesHook
        (lookup: Lookup)
        (resources: IResourceAPI<_>)
        (embeddedSettings: EmbeddedSettings)
        =
        addModifiersFromCoreAndTypes lookup embeddedSettings resources
        lookup.typeDefInfo <- lookup.typeDefInfo |> addModifiersAsTypes lookup
        addDynamicPlanetKillerOnActions lookup resources

        setCarrierAwareCoreLinks
            lookup
            (lookup.triggers
             @ lookup.effects
             @ (updateEventTargetLinks embeddedSettings
                @ addDataEventTargetLinks lookup embeddedSettings false))

    let refreshConfigAfterVarDefHook
        (lookup: Lookup)
        (resources: IResourceAPI<_>)
        (embeddedSettings: EmbeddedSettings)
        =
        setCarrierAwareCoreLinks
            lookup
            (lookup.triggers
             @ lookup.effects
             @ (updateEventTargetLinks embeddedSettings
                @ addDataEventTargetLinks lookup embeddedSettings false
                @ savedEventTargetLinks lookup))

    let afterInit (game: GameObject) =
        let ts = updateScriptedTriggers (game)
        setCarrierAwareCoreLinks game.Lookup (ts @ game.Lookup.effects @ game.Lookup.eventTargetLinks)
        let es = updateScriptedEffects (game)
        setCarrierAwareCoreLinks game.Lookup (game.Lookup.triggers @ es @ game.Lookup.eventTargetLinks)
        updateStaticodifiers (game)
        updateScriptedLoc (game)
        // updateModifiers(game)
        updateTechnologies (game)

    let afterUpdateFile (game: GameObject<STLComputedData, STLLookup>) (filepath: string) =
        match filepath with
        | x when x.Contains("scripted_triggers") ->
            let previousTriggerSignature =
                game.Lookup.onlyScriptedTriggers
                |> List.map (effectSemanticSignature "trigger")
                |> List.sort
            let triggers = updateScriptedTriggers game
            let currentTriggerSignature =
                game.Lookup.onlyScriptedTriggers
                |> List.map (effectSemanticSignature "trigger")
                |> List.sort
            if previousTriggerSignature <> currentTriggerSignature then
                setCarrierAwareCoreLinks
                    game.Lookup
                    (triggers @ game.Lookup.effects @ game.Lookup.eventTargetLinks)
                // Scripted effects may call the changed trigger, so refresh their
                // inferred scopes before exposing the new global link map.
                let effects = updateScriptedEffects game
                setCarrierAwareCoreLinks
                    game.Lookup
                    (game.Lookup.triggers @ effects @ game.Lookup.eventTargetLinks)
        | x when x.Contains("scripted_effects") ->
            let previousEffectSignature =
                game.Lookup.onlyScriptedEffects
                |> List.map (effectSemanticSignature "effect")
                |> List.sort
            let effects = updateScriptedEffects game
            let currentEffectSignature =
                game.Lookup.onlyScriptedEffects
                |> List.map (effectSemanticSignature "effect")
                |> List.sort
            if previousEffectSignature <> currentEffectSignature then
                setCarrierAwareCoreLinks
                    game.Lookup
                    (game.Lookup.triggers @ effects @ game.Lookup.eventTargetLinks)
        | x when x.Contains("scripted_loc") -> updateScriptedLoc game
        | x when x.Contains("static_modifiers") -> updateStaticodifiers game
        | _ -> ()

    [<Literal>]
    let private PlanetHost = 1

    [<Literal>]
    let private ShipHost = 2

    [<Literal>]
    let private AnyCarrierHost = 3

    type private CarrierInferenceSnapshot =
        { version: int
          eventHosts: Map<string, int>
          eventEvidence: Map<string, string list>
          eventFromChains: Map<string, Set<Scope list>>
          eventSavedTargetScopes: Map<string, Map<string, Set<Scope>>>
          globalSavedTargetScopes: Map<string, Set<Scope>>
          projectCreationScopes: Map<string, Set<Scope>>
          projectLocationScopes: Map<string, Set<Scope>>
          situationTargetScopes: Map<string, Set<Scope>>
          situationEventTargetScopes: Map<string, Set<Scope>>
          expandedNodeOwners: Dictionary<Node, struct (Entity * Node)> }

    type internal CarrierScopeResolver
        (
            resources: IResourceAPI<STLComputedData>,
            lookup: STLLookup,
            getInfoService: unit -> InfoService option
        ) =

        let gate = obj ()
        let mutable building = false
        let mutable cached: CarrierInferenceSnapshot option = None
        let mutable buildingExpandedNodeOwners: Dictionary<Node, struct (Entity * Node)> option = None
        let emptyVars = CWTools.Utilities.Utils2.PrefixOptimisedStringSet()

        let emptyExpandedNodeOwners () =
            Dictionary<Node, struct (Entity * Node)>(HashIdentity.Reference)

        let scopeByName name =
            scopeManager.AllScopes
            |> List.tryFind (fun scope ->
                String.Equals(scopeManager.GetName scope, name, StringComparison.OrdinalIgnoreCase))

        let planetScope () = scopeByName "Planet"
        let shipScope () = scopeByName "Ship"
        let carrierScope () = scopeByName "Carrier"
        let colonyScope () = scopeByName "Colony"
        let countryScope () = scopeByName "Country"

        let scopeName (scope: Scope) = scopeManager.GetName scope

        let isScope name scope =
            String.Equals(scopeName scope, name, StringComparison.OrdinalIgnoreCase)

        let hostMaskOfScope scope =
            if isScope "Planet" scope then PlanetHost
            elif isScope "Ship" scope then ShipHost
            elif isScope "Carrier" scope || isScope "Colony" scope then AnyCarrierHost
            else 0

        let hostScope mask =
            match mask with
            | PlanetHost -> planetScope ()
            | ShipHost -> shipScope ()
            | AnyCarrierHost -> carrierScope ()
            | _ -> None

        let setCurrent current (context: ScopeContext) =
            let scopes =
                match context.Scopes with
                | [] -> [ current ]
                | _ :: tail -> current :: tail

            { context with Scopes = scopes }

        let setCarrierHost current (context: ScopeContext) =
            let root =
                if isScope "Carrier" context.Root then current else context.Root

            { setCurrent current context with Root = root }

        let normalizeKey (key: string) =
            let key = key.Trim().Trim('"').ToLowerInvariant()
            if key.StartsWith("hidden:") then key.Substring(7) else key

        let cleanValue (value: string) =
            if isNull value then "" else value.Trim().Trim('"')

        let addScope key scope map =
            if String.IsNullOrWhiteSpace key || scope.Equals scopeManager.AnyScope || scope.Equals scopeManager.InvalidScope then
                map
            else
                map
                |> Map.change (key.ToLowerInvariant()) (fun existing ->
                        existing |> Option.defaultValue Set.empty |> Set.add scope |> Some)

        let addEventTargetScope eventId targetName scope map =
            if String.IsNullOrWhiteSpace eventId || String.IsNullOrWhiteSpace targetName then
                map
            else
                map
                |> Map.change (eventId.ToLowerInvariant()) (fun existing ->
                    existing
                    |> Option.defaultValue Map.empty
                    |> addScope targetName scope
                    |> Some)

        let addMask key mask map =
            if String.IsNullOrWhiteSpace key || mask = 0 then map
            else
                map
                |> Map.change (key.ToLowerInvariant()) (fun existing ->
                    Some((existing |> Option.defaultValue 0) ||| mask))

        let addEvidence key evidence map =
            if String.IsNullOrWhiteSpace key || String.IsNullOrWhiteSpace evidence then map
            else
                map
                |> Map.change (key.ToLowerInvariant()) (fun existing ->
                    Some(evidence :: (existing |> Option.defaultValue []) |> List.distinct))

        let addFromChain key (chain: Scope list) map =
            let chain = chain |> Seq.truncate 4 |> Seq.toList
            if String.IsNullOrWhiteSpace key || chain.IsEmpty then map
            else
                map
                |> Map.change (key.ToLowerInvariant()) (fun existing ->
                    let updated = existing |> Option.defaultValue Set.empty |> Set.add chain
                    if updated.Count <= 256 then
                        Some updated
                    else
                        // Highly connected event graphs must stay bounded; overflow
                        // falls back conservatively instead of selecting one call path.
                        let depth = updated |> Seq.map List.length |> Seq.max
                        Some(Set.singleton(List.replicate depth scopeManager.AnyScope)))

        let chooseScope (scopes: Set<Scope>) =
            if scopes.Count = 1 then
                scopes |> Seq.tryHead
            else
                let mask = scopes |> Seq.fold (fun acc scope -> acc ||| hostMaskOfScope scope) 0
                if mask = AnyCarrierHost && scopes |> Seq.forall (fun scope -> hostMaskOfScope scope <> 0) then
                    carrierScope ()
                else
                    Some scopeManager.AnyScope

        let mergeFromChains (chains: Set<Scope list>) =
            let depth = chains |> Seq.map List.length |> Seq.append [ 0 ] |> Seq.max |> min 4
            [ 0 .. depth - 1 ]
            |> List.map (fun index ->
                chains
                |> Seq.choose (List.tryItem index)
                |> Set.ofSeq
                |> chooseScope
                |> Option.defaultValue scopeManager.AnyScope)

        let rec allNodes (node: Node) =
            seq {
                yield node
                for child in node.Nodes do
                    yield! allNodes child
            }

        let tryPathTo (target: Node) (root: Node) =
            let rec loop path (node: Node) =
                if node.Position.Equals target.Position then
                    Some(List.rev (node :: path))
                else
                    node.Nodes
                    |> Seq.tryPick (fun child ->
                        if rangeContainsRange child.Position target.Position then
                            loop (node :: path) child
                        else
                            None)

            loop [] root

        let tryStaticContextAt (entity: Entity) (position: range) =
            getInfoService ()
            |> Option.bind (fun info ->
                let pos = mkPos position.StartLine (int position.StartColumn)
                info.GetInfo(pos, entity) |> Option.map fst)

        let tryStaticContext (entity: Entity) (node: Node) =
            tryStaticContextAt entity node.Position

        let contextFromReplaceScopes (replaceScopes: ReplaceScopes) =
            let root =
                replaceScopes.root
                |> Option.orElse replaceScopes.this
                |> Option.defaultValue scopeManager.AnyScope

            let prevs = replaceScopes.prevs |> Option.defaultValue []
            let scopes = replaceScopes.this |> Option.map (fun current -> current :: prevs) |> Option.defaultValue prevs

            { Root = root
              From = replaceScopes.froms |> Option.defaultValue []
              FromDepth = 0
              FromDepthStack = []
              Scopes = scopes }

        let trySubtypeContext typeName (root: Node) =
            let subtypeMatches (subtype: SubTypeDefinition) =
                let key = root.Key
                let fieldMatches =
                    subtype.typeKeyField
                    |> Option.forall (fun field -> String.Equals(field, key, StringComparison.OrdinalIgnoreCase))

                let prefixMatches =
                    subtype.startsWith
                    |> Option.forall (fun prefix -> key.StartsWith(prefix, StringComparison.OrdinalIgnoreCase))

                let regexMatches =
                    subtype.typeKeyRegex
                    |> Option.forall (fun pattern ->
                        System.Text.RegularExpressions.Regex.IsMatch(
                            key,
                            pattern,
                            System.Text.RegularExpressions.RegexOptions.IgnoreCase
                        ))

                fieldMatches && prefixMatches && regexMatches

            lookup.typeDefs
            |> List.filter (fun definition -> String.Equals(definition.name, typeName, StringComparison.OrdinalIgnoreCase))
            |> List.collect (fun definition -> definition.subtypes)
            |> List.filter subtypeMatches
            |> List.tryPick (fun subtype ->
                match subtype.replaceScopes, subtype.pushScope with
                | Some scopes, _ -> Some(contextFromReplaceScopes scopes)
                | None, Some scope ->
                    Some
                        { Root = scope
                          From = []
                          FromDepth = 0
                          FromDepthStack = []
                          Scopes = [ scope ] }
                | None, None -> None)

        let changeContextByKey (key: string) (context: ScopeContext) =
            match
                changeScope.Invoke(
                    false,
                    true,
                    lookup.eventTargetLinksMap,
                    lookup.valueTriggerMap,
                    [],
                    emptyVars,
                    key.AsSpan(),
                    context
                )
            with
            | ScopeResult.NewScope(newContext, _, _) -> newContext
            | _ -> context

        let contextAtNodeFromRoot typeName (root: Node) (target: Node) =
            trySubtypeContext typeName root
            |> Option.map (fun rootContext ->
                tryPathTo target root
                |> Option.map (fun path ->
                    path
                    |> List.tail
                    |> List.rev
                    |> List.tail
                    |> List.rev
                    |> List.fold (fun context node -> changeContextByKey node.Key context) rootContext)
                |> Option.defaultValue rootContext)

        let contextInsideNodeFromRoot (rootContext: ScopeContext) (root: Node) (target: Node) =
            tryPathTo target root
            |> Option.map (fun path ->
                path
                |> List.tail
                |> List.fold (fun context node -> changeContextByKey node.Key context) rootContext)
            |> Option.defaultValue rootContext

        let resolveExpression (context: ScopeContext) value =
            let value = cleanValue value
            if String.IsNullOrWhiteSpace value then context.CurrentScope
            else (changeContextByKey value context).CurrentScope

        let setChainItem index value chain =
            let missing = index - List.length chain + 1
            let padded = if missing > 0 then chain @ List.replicate missing scopeManager.AnyScope else chain
            padded |> List.mapi (fun itemIndex existing -> if itemIndex = index then value else existing)

        let eventFromChain (context: ScopeContext) (eventCall: Node) =
            // Without an explicit scopes.from override, fired events inherit the
            // firing event's ROOT as FROM, even when the call is inside an iterator.
            let defaultChain = context.Root :: context.From

            eventCall.Nodes
            |> Seq.tryFind (fun child -> normalizeKey child.Key = "scopes")
            |> Option.map (fun scopes ->
                [ 0, "from"; 1, "fromfrom"; 2, "fromfromfrom"; 3, "fromfromfromfrom" ]
                |> List.fold (fun chain (index, key) ->
                    let expression = scopes.TagText key |> cleanValue
                    if String.IsNullOrWhiteSpace expression then chain
                    else setChainItem index (resolveExpression context expression) chain) defaultChain
                |> Seq.truncate 4
                |> Seq.toList)
            |> Option.defaultValue defaultChain

        let rec conditionHostMask negated (node: Node) =
            let key = normalizeKey node.Key

            if key = "or" || key = "nor" || key = "nand" then
                0
            else
                let direct =
                    node.Leaves
                    |> Seq.choose (fun leaf ->
                        if String.Equals(leaf.Key, "carrier_is_type", StringComparison.OrdinalIgnoreCase) then
                            match cleanValue leaf.ValueText |> fun value -> value.ToLowerInvariant() with
                            | "planet" -> Some(if negated then ShipHost else PlanetHost)
                            | "ship" -> Some(if negated then PlanetHost else ShipHost)
                            | _ -> None
                        else
                            None)
                    |> Seq.distinct
                    |> Seq.toList

                let nested =
                    node.Nodes
                    |> Seq.map (fun child ->
                        conditionHostMask (if normalizeKey child.Key = "not" then not negated else negated) child)
                    |> Seq.filter ((<>) 0)
                    |> Seq.distinct
                    |> Seq.toList

                match direct @ nested |> List.distinct with
                | [ mask ] -> mask
                | _ -> 0

        let impliedHostMask (node: Node) =
            let key = normalizeKey node.Key
            let conditionKeys = set [ "limit"; "trigger"; "potential"; "allow" ]

            if conditionKeys.Contains key then
                conditionHostMask false node
            else
                node.Nodes
                |> Seq.filter (fun child -> conditionKeys.Contains(normalizeKey child.Key))
                |> Seq.map (conditionHostMask false)
                |> Seq.filter ((<>) 0)
                |> Seq.distinct
                |> Seq.toList
                |> function
                    | [ mask ] -> mask
                    | _ -> 0

        let callbackKeys =
            set
                [ "fail_trigger"
                  "abort_trigger"
                  "on_success"
                  "on_progress_25"
                  "on_progress_50"
                  "on_progress_75"
                  "on_start"
                  "on_fail"
                  "on_cancel" ]

        let hasLogicalPathSegment (segment: string) (entity: Entity) =
            let logicalPath = entity.logicalpath.Replace('\\', '/').TrimStart('/')
            let segment = segment.Trim('/').TrimEnd('/') + "/"

            logicalPath.StartsWith(segment, StringComparison.OrdinalIgnoreCase)
            || logicalPath.Contains("/" + segment, StringComparison.OrdinalIgnoreCase)

        let isSpecialProjectPath (entity: Entity) =
            hasLogicalPathSegment "common/special_projects" entity

        let isSituationPath (entity: Entity) =
            hasLogicalPathSegment "common/situations" entity

        let isOnActionPath (entity: Entity) =
            hasLogicalPathSegment "common/on_actions" entity

        let isEventPath (entity: Entity) =
            hasLogicalPathSegment "events" entity

        let projectIdOfRoot (root: Node) =
            let key = root.TagText "key" |> cleanValue
            if String.IsNullOrWhiteSpace key then root.Key else key

        let eventScopeForProject (projectId: string) (root: Node) projectCreationScopes projectLocationScopes =
            let eventScope = root.TagText "event_scope" |> cleanValue |> fun value -> value.ToLowerInvariant()
            match eventScope with
            | "planet_event" -> planetScope ()
            | "ship_event" -> shipScope ()
            | "country_event" -> countryScope ()
            | "colony_event" -> colonyScope ()
            | "carrier_event" ->
                projectLocationScopes
                |> Map.tryFind (projectId.ToLowerInvariant())
                |> Option.bind chooseScope
                |> Option.orElseWith (fun () ->
                    projectCreationScopes
                    |> Map.tryFind (projectId.ToLowerInvariant())
                    |> Option.bind chooseScope)
                |> Option.bind (fun scope ->
                    if hostMaskOfScope scope = 0 then carrierScope () else Some scope)
                |> Option.orElseWith (fun () -> carrierScope ())
            | _ -> None

        let projectCallbackContext
            (projectId: string)
            (root: Node)
            callbackKey
            projectCreationScopes
            projectLocationScopes
            (fallback: ScopeContext)
            =
            let eventScope =
                eventScopeForProject projectId root projectCreationScopes projectLocationScopes
                |> Option.defaultValue scopeManager.AnyScope

            let creationScope =
                projectCreationScopes
                |> Map.tryFind (projectId.ToLowerInvariant())
                |> Option.bind chooseScope
                |> Option.defaultValue scopeManager.AnyScope

            let ownerScope = countryScope () |> Option.defaultValue scopeManager.AnyScope

            let current, callbackRoot, froms =
                match callbackKey with
                | "on_success"
                | "on_progress_25"
                | "on_progress_50"
                | "on_progress_75"
                | "on_start" -> eventScope, eventScope, [ creationScope ]
                | "fail_trigger"
                | "abort_trigger" ->
                    ownerScope, ownerScope, [ eventScope; creationScope ]
                | "on_fail"
                | "on_cancel" ->
                    ownerScope, ownerScope, [ eventScope; creationScope ]
                | _ -> fallback.CurrentScope, fallback.Root, fallback.From

            let resolved =
                { setCurrent current fallback with
                    Root = callbackRoot
                    From = froms
                    FromDepth = 0
                    FromDepthStack = [] }

            match callbackKey with
            | "on_success"
            | "on_progress_25"
            | "on_progress_50"
            | "on_progress_75"
            | "on_start" -> { resolved with Scopes = [ eventScope; ownerScope ] }
            | _ -> resolved

        let callbackContextAt
            projectId
            (root: Node)
            (target: Node)
            projectCreationScopes
            projectLocationScopes
            fallback
            =
            root.Nodes
            |> Seq.tryFind (fun callback ->
                callbackKeys.Contains(normalizeKey callback.Key)
                && rangeContainsRange callback.Position target.Position)
            |> Option.map (fun callback ->
                let baseContext =
                    projectCallbackContext
                        projectId
                        root
                        (normalizeKey callback.Key)
                        projectCreationScopes
                        projectLocationScopes
                        fallback

                tryPathTo target callback
                |> Option.map (fun path ->
                    path
                    |> List.tail
                    |> List.rev
                    |> List.tail
                    |> List.rev
                    |> List.fold (fun context node -> changeContextByKey node.Key context) baseContext)
                |> Option.defaultValue baseContext)

        let buildSnapshot version =
            let entities =
                resources.AllEntities()
                |> Seq.map (fun struct (entity, _) -> entity)
                |> Seq.toArray

            // Expanded inline-script nodes keep the template's source range. Keep
            // their concrete caller/root ownership by object identity so contextual
            // event-target inference does not jump back to the unexpanded template.
            let expandedNodeOwners = emptyExpandedNodeOwners ()

            for entity in entities do
                for root in entity.entity.Nodes do
                    for node in allNodes root do
                        if
                            not (String.IsNullOrWhiteSpace node.Position.FileName)
                            && not (String.Equals(node.Position.FileName, entity.filepath, StringComparison.OrdinalIgnoreCase))
                        then
                            expandedNodeOwners[node] <- struct (entity, root)

            buildingExpandedNodeOwners <- Some expandedNodeOwners
            let eventDefinitions = Dictionary<string, struct (Entity * Node)>(StringComparer.OrdinalIgnoreCase)
            let carrierEventIds = HashSet<string>(StringComparer.OrdinalIgnoreCase)

            for entity in entities do
                if isEventPath entity then
                    for root in entity.entity.Nodes do
                        let eventId = root.TagText "id" |> cleanValue
                        if not (String.IsNullOrWhiteSpace eventId) && (normalizeKey root.Key).EndsWith("_event") then
                            eventDefinitions[eventId] <- struct (entity, root)
                            if normalizeKey root.Key = "carrier_event" then carrierEventIds.Add eventId |> ignore

            let mutable projectCreationScopes: Map<string, Set<Scope>> = Map.empty
            let mutable projectLocationScopes: Map<string, Set<Scope>> = Map.empty
            let mutable situationScopes: Map<string, Set<Scope>> = Map.empty

            for entity in entities do
                for root in entity.entity.Nodes do
                    for node in allNodes root do
                        match normalizeKey node.Key with
                        | "enable_special_project" ->
                            let id = node.TagText "name" |> cleanValue
                            let nodeContext =
                                tryStaticContext entity node
                                |> Option.orElseWith (fun () ->
                                    if isEventPath entity then contextAtNodeFromRoot "event" root node else None)

                            match nodeContext with
                            | Some context when not (String.IsNullOrWhiteSpace id) ->
                                let location = node.TagText "location"
                                projectCreationScopes <- addScope id context.CurrentScope projectCreationScopes
                                if not (String.IsNullOrWhiteSpace(cleanValue location)) then
                                    projectLocationScopes <-
                                        addScope id (resolveExpression context location) projectLocationScopes
                            | _ -> ()
                        | "start_situation" ->
                            let id = node.TagText "type" |> cleanValue
                            let target = node.TagText "target"
                            let nodeContext =
                                tryStaticContext entity node
                                |> Option.orElseWith (fun () ->
                                    if isEventPath entity then contextAtNodeFromRoot "event" root node else None)

                            match nodeContext with
                            | Some context when not (String.IsNullOrWhiteSpace id) && not (String.IsNullOrWhiteSpace target) ->
                                situationScopes <- addScope id (resolveExpression context target) situationScopes
                            | _ -> ()
                        | _ -> ()

            let mutable situationEventTargetScopes: Map<string, Set<Scope>> = Map.empty

            for entity in entities do
                if isSituationPath entity then
                    for root in entity.entity.Nodes do
                        match situationScopes |> Map.tryFind (root.Key.ToLowerInvariant()) with
                        | Some targets ->
                            for node in allNodes root do
                                if normalizeKey node.Key = "situation_event" then
                                    let eventId = node.TagText "id" |> cleanValue
                                    for target in targets do
                                        situationEventTargetScopes <-
                                            addScope eventId target situationEventTargetScopes
                        | None -> ()

            let mutable seeds: Map<string, int> = Map.empty
            let mutable evidence: Map<string, string list> = Map.empty
            let mutable eventFromChains: Map<string, Set<Scope list>> = Map.empty
            let carrierDependencies = ResizeArray<string * string * Node * ScopeContext>()
            let eventDependencies = ResizeArray<string * string * Node * ScopeContext>()

            for pair in eventDefinitions do
                let eventId = pair.Key
                let struct (_, root) = pair.Value

                if carrierEventIds.Contains eventId then
                    let mask = impliedHostMask root
                    if mask <> 0 then
                        seeds <- addMask eventId mask seeds
                        evidence <- addEvidence eventId $"carrier_is_type in %s{root.Position.FileName}:%i{root.Position.StartLine}" evidence

            for entity in entities do
                for root in entity.entity.Nodes do
                    let rootEventId = root.TagText "id" |> cleanValue
                    let callerEventId =
                        if (normalizeKey root.Key).EndsWith("_event") && eventDefinitions.ContainsKey rootEventId then
                            Some rootEventId
                        else
                            None

                    let callerCarrierId =
                        if normalizeKey root.Key = "carrier_event" && carrierEventIds.Contains rootEventId then Some rootEventId else None

                    for node in allNodes root do
                        if (normalizeKey node.Key).EndsWith("_event") && not (node.Position.Equals root.Position) then
                            let targetId = node.TagText "id" |> cleanValue
                            if eventDefinitions.ContainsKey targetId then
                                let staticContext =
                                    tryStaticContext entity node
                                    |> Option.orElseWith (fun () ->
                                        if isEventPath entity then contextAtNodeFromRoot "event" root node else None)
                                    |> Option.defaultValue
                                        { Root = scopeManager.AnyScope
                                          From = []
                                          FromDepth = 0
                                          FromDepthStack = []
                                          Scopes = [] }

                                let context =
                                    if isSpecialProjectPath entity then
                                        callbackContextAt
                                            (projectIdOfRoot root)
                                            root
                                            node
                                            projectCreationScopes
                                            projectLocationScopes
                                            staticContext
                                        |> Option.defaultValue staticContext
                                    else
                                        staticContext

                                match callerEventId with
                                | Some caller ->
                                    eventDependencies.Add(caller, targetId, node, context)

                                    let staticChain = eventFromChain context node
                                    match staticChain with
                                    | first :: _
                                        when callerCarrierId.IsNone
                                             && not (first.Equals scopeManager.AnyScope) ->
                                        eventFromChains <- addFromChain targetId staticChain eventFromChains
                                    | _ -> ()
                                | None ->
                                    eventFromChains <- addFromChain targetId (eventFromChain context node) eventFromChains

                                if carrierEventIds.Contains targetId then
                                    let mask = hostMaskOfScope context.CurrentScope
                                    match callerCarrierId, mask, isScope "Carrier" context.Root with
                                    | Some caller, AnyCarrierHost, true -> carrierDependencies.Add(caller, targetId, node, context)
                                    | _, 0, _ ->
                                        seeds <- addMask targetId AnyCarrierHost seeds
                                        evidence <- addEvidence targetId $"unknown caller at %s{node.Position.FileName}:%i{node.Position.StartLine}" evidence
                                    | _, value, _ ->
                                        seeds <- addMask targetId value seeds
                                        evidence <-
                                            addEvidence
                                                targetId
                                                $"%s{scopeName context.CurrentScope} caller at %s{node.Position.FileName}:%i{node.Position.StartLine}"
                                                evidence

                    if isOnActionPath entity then
                        let eventListNodes =
                            allNodes root
                            |> Seq.filter (fun node ->
                                let key = normalizeKey node.Key
                                key = "events" || key = "random_events")

                        for eventList in eventListNodes do
                            let listContext =
                                trySubtypeContext "on_action" root
                                |> Option.orElseWith (fun () -> tryStaticContext entity eventList)
                                |> Option.defaultValue
                                    { Root = scopeManager.AnyScope
                                      From = []
                                      FromDepth = 0
                                      FromDepthStack = []
                                      Scopes = [] }

                            let mask = hostMaskOfScope listContext.CurrentScope

                            for value in eventList.LeafValues do
                                let targetId = cleanValue value.ValueText
                                if eventDefinitions.ContainsKey targetId then
                                    eventFromChains <- addFromChain targetId listContext.From eventFromChains
                                    if carrierEventIds.Contains targetId then
                                        seeds <- addMask targetId (if mask = 0 then AnyCarrierHost else mask) seeds
                                        evidence <- addEvidence targetId $"on_action %s{root.Key} (%s{scopeName listContext.CurrentScope})" evidence

                            for value in eventList.Leaves do
                                let targetId = cleanValue value.ValueText
                                if eventDefinitions.ContainsKey targetId then
                                    eventFromChains <- addFromChain targetId listContext.From eventFromChains
                                    if carrierEventIds.Contains targetId then
                                        seeds <- addMask targetId (if mask = 0 then AnyCarrierHost else mask) seeds
                                        evidence <- addEvidence targetId $"on_action %s{root.Key} (%s{scopeName listContext.CurrentScope})" evidence

            let mutable eventHosts = seeds
            let mutable changed = true
            let mutable iterations = 0
            while changed && iterations < 64 do
                changed <- false
                iterations <- iterations + 1

                for caller, target, eventCall, staticContext in eventDependencies do
                    let callerChains =
                        eventFromChains
                        |> Map.tryFind (caller.ToLowerInvariant())
                        |> Option.defaultValue Set.empty

                    for chain in callerChains do
                        let callerContext =
                            let withFrom =
                                { staticContext with
                                    From = chain
                                    FromDepth = 0
                                    FromDepthStack = [] }
                            let callerMask = eventHosts |> Map.tryFind (caller.ToLowerInvariant()) |> Option.defaultValue 0
                            match hostScope callerMask with
                            | Some callerScope -> setCarrierHost callerScope withFrom
                            | None -> withFrom

                        let beforeChains =
                            eventFromChains
                            |> Map.tryFind (target.ToLowerInvariant())
                            |> Option.defaultValue Set.empty

                        eventFromChains <- addFromChain target (eventFromChain callerContext eventCall) eventFromChains

                        let afterChains =
                            eventFromChains
                            |> Map.tryFind (target.ToLowerInvariant())
                            |> Option.defaultValue Set.empty

                        if afterChains <> beforeChains then changed <- true

                for caller, target, _, _ in carrierDependencies do
                    let callerMask = eventHosts |> Map.tryFind (caller.ToLowerInvariant()) |> Option.defaultValue 0
                    if callerMask <> 0 then
                        let before = eventHosts |> Map.tryFind (target.ToLowerInvariant()) |> Option.defaultValue 0
                        let after = before ||| callerMask
                        if after <> before then
                            eventHosts <- addMask target callerMask eventHosts
                            evidence <- addEvidence target $"carrier_event from %s{caller}" evidence
                            changed <- true

            let mutable directEventSavedTargetScopes: Map<string, Map<string, Set<Scope>>> = Map.empty
            let mutable globalSavedTargetScopes: Map<string, Set<Scope>> = Map.empty

            // ComputedData already records the scope at each concrete save site,
            // including parameter-substituted inline-script expansions. Index it
            // by target name so the event graph only has to add lifetime/ownership
            // association instead of re-inferring a duplicated template range.
            let savedTargetScopesByName =
                lookup.savedEventTargets
                |> Seq.groupBy (fun (name, _, _) -> name.ToLowerInvariant())
                |> Seq.map (fun (name, saves) -> name, saves |> Seq.toArray)
                |> Map.ofSeq

            // Rule-driven iterators such as random_owned_planet can only be
            // interpreted by the completed InfoService. During early game
            // construction, leave target bindings unresolved and rebuild this
            // snapshot once InfoService is available instead of recording the
            // event root scope as false evidence.
            if getInfoService().IsSome then
                for pair in eventDefinitions do
                    let eventId = pair.Key
                    let struct (entity, root) = pair.Value
                    let rootContext =
                        trySubtypeContext "event" root
                        |> Option.defaultValue
                            { Root = scopeManager.AnyScope
                              From = []
                              FromDepth = 0
                              FromDepthStack = []
                              Scopes = [] }

                    let rootContext =
                        match eventFromChains |> Map.tryFind (eventId.ToLowerInvariant()) with
                        | Some chains when not chains.IsEmpty ->
                            { rootContext with
                                From = mergeFromChains chains
                                FromDepth = 0
                                FromDepthStack = [] }
                        | _ -> rootContext

                    let rootContext =
                        let mask = eventHosts |> Map.tryFind (eventId.ToLowerInvariant()) |> Option.defaultValue 0
                        match hostScope mask with
                        | Some eventScope -> setCarrierHost eventScope rootContext
                        | None -> rootContext

                    for node in allNodes root do
                        // Expanded inline-script nodes retain the source inline
                        // file's range; their call-site scope is handled by the
                        // normal expansion pass.
                        if rangeContainsRange root.Position node.Position then
                            let pathContext = contextInsideNodeFromRoot rootContext root node
                            let isExpandedNode = expandedNodeOwners.ContainsKey node
                            for leaf in node.Leaves do
                                let key = normalizeKey leaf.Key
                                if key = "save_event_target_as" || key = "save_global_event_target_as" then
                                    let targetName = cleanValue leaf.ValueText
                                    let canonicalSavedScope =
                                        savedTargetScopesByName
                                        |> Map.tryFind (targetName.ToLowerInvariant())
                                        |> Option.map (fun saves ->
                                            saves
                                            |> Seq.choose (fun (_, position, scope) ->
                                                if position.Equals leaf.Position then Some scope else None)
                                            |> Set.ofSeq)
                                        |> Option.filter (fun scopes -> not scopes.IsEmpty)
                                        |> Option.bind chooseScope
                                        |> Option.filter (fun scope ->
                                            not (scope.Equals scopeManager.AnyScope)
                                            && not (scope.Equals scopeManager.InvalidScope))

                                    let pathNodeContext =
                                        if
                                            pathContext.CurrentScope.Equals scopeManager.AnyScope
                                            || pathContext.CurrentScope.Equals scopeManager.InvalidScope
                                        then
                                            None
                                        else
                                            Some pathContext

                                    let nodeContext =
                                        match canonicalSavedScope with
                                        | Some scope -> Some(setCurrent scope pathContext)
                                        | None when isExpandedNode ->
                                            // The template range may occur in several
                                            // expansions inside the same caller file.
                                            // A positional InfoService lookup can then
                                            // select a different event root and report
                                            // its Country scope. The concrete expanded
                                            // root/path is unambiguous here.
                                            pathNodeContext
                                        | None ->
                                            tryStaticContextAt entity leaf.Position
                                            |> Option.filter (fun context ->
                                                not (context.CurrentScope.Equals scopeManager.AnyScope)
                                                && not (context.CurrentScope.Equals scopeManager.InvalidScope))
                                            |> Option.orElseWith (fun () -> pathNodeContext)

                                    match nodeContext with
                                    | Some nodeContext when key = "save_global_event_target_as" ->
                                        globalSavedTargetScopes <-
                                            addScope targetName nodeContext.CurrentScope globalSavedTargetScopes
                                    | Some nodeContext ->
                                        directEventSavedTargetScopes <-
                                            addEventTargetScope
                                                eventId
                                                targetName
                                                nodeContext.CurrentScope
                                                directEventSavedTargetScopes
                                    | None -> ()

            // Ordinary event targets are inherited only by events reached from
            // the saving event. A directly saved name in the callee shadows the
            // inherited binding, while multiple callers are merged conservatively.
            let mutable eventSavedTargetScopes = directEventSavedTargetScopes
            let mutable targetScopesChanged = true
            let mutable targetScopeIterations = 0

            while targetScopesChanged && targetScopeIterations < 64 do
                targetScopesChanged <- false
                targetScopeIterations <- targetScopeIterations + 1

                for caller, target, _, _ in eventDependencies do
                    let callerTargets =
                        eventSavedTargetScopes
                        |> Map.tryFind (caller.ToLowerInvariant())
                        |> Option.defaultValue Map.empty

                    let targetKey = target.ToLowerInvariant()
                    let directTargetNames =
                        directEventSavedTargetScopes
                        |> Map.tryFind targetKey
                        |> Option.defaultValue Map.empty

                    let before =
                        eventSavedTargetScopes
                        |> Map.tryFind targetKey
                        |> Option.defaultValue Map.empty

                    let after =
                        callerTargets
                        |> Map.fold (fun targetScopes targetName scopes ->
                            if directTargetNames.ContainsKey targetName then
                                targetScopes
                            else
                                scopes
                                |> Set.fold (fun state scope -> addScope targetName scope state) targetScopes) before

                    if after <> before then
                        eventSavedTargetScopes <- eventSavedTargetScopes |> Map.add targetKey after
                        targetScopesChanged <- true

            { version = version
              eventHosts = eventHosts
              eventEvidence = evidence
              eventFromChains = eventFromChains
              eventSavedTargetScopes = eventSavedTargetScopes
              globalSavedTargetScopes = globalSavedTargetScopes
              projectCreationScopes = projectCreationScopes
              projectLocationScopes = projectLocationScopes
              situationTargetScopes = situationScopes
              situationEventTargetScopes = situationEventTargetScopes
              expandedNodeOwners = expandedNodeOwners }

        let currentSnapshot () =
            let version = ResourceManagerEager.currentVersion ()
            lock gate (fun () ->
                match cached with
                | Some snapshot when snapshot.version = version -> snapshot
                | _ when building ->
                    { version = version
                      eventHosts = Map.empty
                      eventEvidence = Map.empty
                      eventFromChains = Map.empty
                      eventSavedTargetScopes = Map.empty
                      globalSavedTargetScopes = Map.empty
                      projectCreationScopes = Map.empty
                      projectLocationScopes = Map.empty
                      situationTargetScopes = Map.empty
                      situationEventTargetScopes = Map.empty
                      expandedNodeOwners =
                          buildingExpandedNodeOwners
                          |> Option.defaultWith emptyExpandedNodeOwners }
                | _ ->
                    building <- true
                    try
                        let snapshot = buildSnapshot version
                        cached <- Some snapshot
                        snapshot
                    finally
                        building <- false
                        buildingExpandedNodeOwners <- None)

        let tryEntityAndRoot (snapshot: CarrierInferenceSnapshot) (node: Node) =
            match snapshot.expandedNodeOwners.TryGetValue node with
            | true, struct (entity, root) -> Some(entity, root)
            | _ ->
                resources.GetEntityByFilePath node.Position.FileName
                |> Option.bind (fun struct (entity, _) ->
                    entity.entity.Nodes
                    |> Seq.tryFind (fun root -> rangeContainsRange root.Position node.Position)
                    |> Option.map (fun root -> entity, root))

        member _.Invalidate() =
            lock gate (fun () -> cached <- None)

        member _.Resolve(node: IClause, context: ScopeContext) =
            match node with
            | :? Node as node ->
                let resolve () =
                    // currentSnapshot serialises the initial graph build. Calls from
                    // other validation workers must wait for that build; returning
                    // None while `building` made scope results depend on which file
                    // happened to validate first. Re-entrant calls on the builder
                    // thread are still handled by currentSnapshot's empty snapshot.
                    let snapshot = currentSnapshot ()
                    let mutable resolved = context
                    let mutable changed = false

                    match tryEntityAndRoot snapshot node with
                    | Some(entity, root) ->
                        let rootKey = normalizeKey root.Key
                        if rootKey.EndsWith("_event") && node.Position.Equals root.Position then
                            let eventId = root.TagText "id" |> cleanValue
                            if rootKey = "carrier_event" then
                                let mask = snapshot.eventHosts |> Map.tryFind (eventId.ToLowerInvariant()) |> Option.defaultValue AnyCarrierHost
                                match hostScope mask with
                                | Some exact when mask = PlanetHost || mask = ShipHost ->
                                    resolved <- setCarrierHost exact resolved
                                    changed <- true
                                | _ -> ()

                            match snapshot.eventFromChains |> Map.tryFind (eventId.ToLowerInvariant()) with
                            | Some chains when not chains.IsEmpty ->
                                resolved <-
                                    { resolved with
                                        From = mergeFromChains chains
                                        FromDepth = 0
                                        FromDepthStack = [] }
                                changed <- true
                            | _ -> ()

                        let normalizedNodeKey = normalizeKey node.Key
                        let eventTargetSuffix =
                            if normalizedNodeKey.StartsWith("event_target:") then
                                Some(normalizedNodeKey.Substring("event_target:".Length))
                            else
                                None

                        if rootKey.EndsWith("_event") && eventTargetSuffix.IsSome then
                            let eventId = root.TagText "id" |> cleanValue
                            let targetPath =
                                eventTargetSuffix.Value.Split('.', StringSplitOptions.RemoveEmptyEntries)
                                |> Array.toList

                            let targetName =
                                targetPath
                                |> List.tryHead
                                |> Option.defaultValue ""
                                |> fun name -> name.TrimEnd('?')

                            let localScope =
                                snapshot.eventSavedTargetScopes
                                |> Map.tryFind (eventId.ToLowerInvariant())
                                |> Option.bind (Map.tryFind (targetName.ToLowerInvariant()))
                                |> Option.bind chooseScope

                            let globalScope =
                                snapshot.globalSavedTargetScopes
                                |> Map.tryFind (targetName.ToLowerInvariant())
                                |> Option.bind chooseScope

                            let inferredScope =
                                match localScope with
                                | Some scope -> Some scope
                                | None ->
                                    // A globally saved name can legitimately have
                                    // several runtime types. Do not replace a more
                                    // precise call-site result with that global
                                    // ambiguity; concrete global evidence still
                                    // corrects polluted flat lookup results.
                                    globalScope
                                    |> Option.filter (fun scope ->
                                        not (scope.Equals scopeManager.AnyScope)
                                        || resolved.CurrentScope.Equals scopeManager.AnyScope)

                            match inferredScope with
                            | Some targetScope ->
                                let pathContext =
                                    targetPath
                                    |> List.skip 1
                                    |> List.fold
                                        (fun targetContext link -> changeContextByKey link targetContext)
                                        (setCurrent targetScope resolved)

                                // A dotted scope path resolves each link in order, but
                                // enters the final result as one scope frame. Intermediate
                                // links must not become visible through PREV.
                                resolved <-
                                    { setCurrent pathContext.CurrentScope resolved with
                                        FromDepth = pathContext.FromDepth }
                                changed <- true
                            | _ -> ()

                        if isSpecialProjectPath entity && callbackKeys.Contains(normalizeKey node.Key) then
                            resolved <-
                                projectCallbackContext
                                    (projectIdOfRoot root)
                                    root
                                    (normalizeKey node.Key)
                                    snapshot.projectCreationScopes
                                    snapshot.projectLocationScopes
                                    resolved
                            changed <- true

                        if isSituationPath entity && normalizeKey node.Key = "target" && resolved.CurrentScope.Equals scopeManager.AnyScope then
                            match snapshot.situationTargetScopes |> Map.tryFind (root.Key.ToLowerInvariant()) |> Option.bind chooseScope with
                            | Some target ->
                                resolved <- setCurrent target resolved
                                changed <- true
                            | None -> ()

                        if rootKey = "situation_event" && normalizeKey node.Key = "target" then
                            let eventId = root.TagText "id" |> cleanValue
                            match snapshot.situationEventTargetScopes |> Map.tryFind (eventId.ToLowerInvariant()) |> Option.bind chooseScope with
                            | Some target ->
                                resolved <- setCurrent target resolved
                                changed <- true
                            | None -> ()
                    | None -> ()

                    if isScope "Carrier" resolved.CurrentScope then
                        let mask = impliedHostMask node
                        match hostScope mask with
                        | Some exact when mask = PlanetHost || mask = ShipHost ->
                            resolved <- setCarrierHost exact resolved
                            changed <- true
                        | _ -> ()

                    if changed then Some resolved else None

                resolve ()
            | _ -> None

        member _.EventEvidence (eventId: string) =
            currentSnapshot().eventEvidence
            |> Map.tryFind (eventId.ToLowerInvariant())
            |> Option.defaultValue []

        member _.ScopeEvidence(node: Node) =
            let snapshot = currentSnapshot ()
            let evidence = ResizeArray<string>()
            let mutable carrierRelevant = false

            match tryEntityAndRoot snapshot node with
            | Some(entity, root) ->
                let rootKey = normalizeKey root.Key
                let path = tryPathTo node root |> Option.defaultValue [ root ]

                if rootKey = "carrier_event" then
                    carrierRelevant <- true
                    let eventId = root.TagText "id" |> cleanValue
                    snapshot.eventEvidence
                    |> Map.tryFind (eventId.ToLowerInvariant())
                    |> Option.defaultValue []
                    |> evidence.AddRange

                for ancestor in path do
                    let mask = impliedHostMask ancestor
                    if mask = PlanetHost || mask = ShipHost then
                        carrierRelevant <- true
                        evidence.Add($"carrier_is_type guard at %s{ancestor.Position.FileName}:%i{ancestor.Position.StartLine}")

                if isSpecialProjectPath entity && root.TagText "event_scope" |> cleanValue |> normalizeKey = "carrier_event" then
                    carrierRelevant <- true
                    let projectId = projectIdOfRoot root
                    let creationScopes =
                        snapshot.projectLocationScopes
                        |> Map.tryFind (projectId.ToLowerInvariant())
                        |> Option.defaultValue Set.empty
                        |> Seq.map scopeName
                        |> String.concat " | "

                    evidence.Add($"special_project %s{projectId} event_scope = carrier_event")
                    if not (String.IsNullOrWhiteSpace creationScopes) then
                        evidence.Add($"enable_special_project location scopes: %s{creationScopes}")

                if isSituationPath entity && path |> List.exists (fun ancestor -> normalizeKey ancestor.Key = "target") then
                    let targetScopes =
                        snapshot.situationTargetScopes
                        |> Map.tryFind (root.Key.ToLowerInvariant())
                        |> Option.defaultValue Set.empty
                        |> Seq.filter (fun scope -> hostMaskOfScope scope <> 0)
                        |> Seq.map scopeName
                        |> String.concat " | "

                    if not (String.IsNullOrWhiteSpace targetScopes) then
                        carrierRelevant <- true
                        evidence.Add($"start_situation target scopes for %s{root.Key}: %s{targetScopes}")
            | None -> ()

            carrierRelevant, (evidence |> Seq.distinct |> Seq.toList)

    let createEmbeddedSettings embeddedFiles cachedResourceData (configs: (string * string) list) cachedRuleMetadata =
        initializeScopesAndModifierCategories configs defaultScopeInputs defaultModifiersInputs

        let triggers, effects =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "trigger_docs.log")
            |> Option.map (fun (fn, ft) -> DocsParser.parseDocsFile fn)
            |> Option.bind (function
                | FParsec.CharParsers.ParserResult.Success(p, _, _) ->
                    Some(DocsParser.processDocs scopeManager.ParseScopes p)
                | FParsec.CharParsers.ParserResult.Failure(e, _, _) ->
                    eprintfn "%A" e
                    None)
            |> Option.defaultWith (fun () ->
                Utils.logError "trigger_docs.log was not found in stellaris config"
                ([], []))


        let stlSetupModifiers =
            if configs |> List.exists (fun (fn, _) -> Path.GetFileName fn = "modifiers.log") then
                configs
                |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "modifiers.log")
                |> Option.map (fun (fn, ft) -> StellarisModifierParser.parseLogsFile fn)
                |> Option.bind (function
                    | FParsec.CharParsers.ParserResult.Success(p, _, _) -> Some(StellarisModifierParser.processLogs p)
                    | FParsec.CharParsers.ParserResult.Failure(e, _, _) -> None)
                |> Option.defaultWith (fun () ->
                    Utils.logError "modifiers.log was not found in stellaris config"
                    [])
            else
                configs
                |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "setup.log")
                |> Option.map (fun (fn, ft) -> SetupLogParser.parseLogsFile fn)
                |> Option.bind (function
                    | FParsec.CharParsers.ParserResult.Success(p, _, _) -> Some(SetupLogParser.processLogs p)
                    | FParsec.CharParsers.ParserResult.Failure(e, _, _) -> None)
                |> Option.defaultWith (fun () ->
                    Utils.logError "setup.log was not found in stellaris config"
                    [])

        let stlRulesMods = getActualModifiers configs

        let stlLocCommands =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "localisation.cwt")
            |> Option.map (fun (fn, ft) -> UtilityParser.loadLocCommands fn ft)
            |> Option.defaultValue ([], [], [])

        let stlEventTargetLinks =
            configs
            |> List.tryFind (fun (fn, _) -> Path.GetFileName fn = "links.cwt")
            |> Option.map (fun (fn, ft) ->
                UtilityParser.loadEventTargetLinks
                    scopeManager.AnyScope
                    (scopeManager.ParseScope())
                    scopeManager.AllScopes
                    fn
                    ft)
            |> Option.defaultValue []

        let featureSettings = getFeatureSettings configs

        { triggers = triggers
          effects = effects
          modifiers = stlSetupModifiers.Concat(stlRulesMods).ToArray()
          embeddedFiles = embeddedFiles
          cachedResourceData = cachedResourceData
          localisationCommands = Legacy stlLocCommands
          eventTargetLinks = stlEventTargetLinks
          cachedRuleMetadata = cachedRuleMetadata
          featureSettings = featureSettings }


type StellarisSettings = GameSetupSettings<STLLookup>

open STLGameFunctions

type STLGame(setupSettings: StellarisSettings) =
    let validationSettings =
        { validators =
            [ validateVariables, "var"
              valTechnology, "tech"
              validateShipDesigns, "designs"
              validateIfElse, "ifelse2"
              validateNOTMultiple, "notmultiple"
              validatePlanetKillers, "pk"
              validateRedundantANDWithNOR, "AND"
              valMegastructureGraphics, "megastructure"
              valPlanetClassGraphics, "pcg"
              validateDeprecatedSetName, "setname"
              validateScriptedActionScopeOrder, "scriptedactionscopeorder"
              validateEvents, "eventsSimple"
              validatePreTriggers, "pre"
              validateIfWithNoEffect, "ifnoeffect" ]
          experimentalValidators = [ valSectionGraphics, "sections"; valComponentGraphics, "component" ]
          heavyExperimentalValidators = [ getEventChains, "event chains" ]
          experimental = setupSettings.validation.experimental
          fileValidators = [ validateTechnologies, "tech2" ]
          lookupValidators = (validateEconomicCatAIBudget, "aibudget") :: commonValidationRules
          lookupFileValidators =
            [ valScriptedEffectParams, "scripted_effects"
              valScriptValueParams, "script_values" ]
          useRules =
            setupSettings.rules
            |> Option.map (fun o -> o.validateRules)
            |> Option.defaultValue false
          debugRulesOnly =
            setupSettings.rules
            |> Option.map (fun o -> o.debugRulesOnly)
            |> Option.defaultValue false
          localisationValidators = [ valTechLocs; valPolicies ]

        }

    let embeddedSettings =
        match setupSettings.embedded with
        | FromConfig(ef, crd) ->
            createEmbeddedSettings
                ef
                crd
                (setupSettings.rules
                 |> Option.map (fun r -> r.ruleFiles)
                 |> Option.defaultValue [])
                None
        | Metadata cmd ->
            createEmbeddedSettings
                []
                []
                (setupSettings.rules
                 |> Option.map (fun r -> r.ruleFiles)
                 |> Option.defaultValue [])
                (Some cmd)
        | ManualSettings e -> e

    let settings =
        { rootDirectories = setupSettings.rootDirectories
          excludeGlobPatterns = setupSettings.excludeGlobPatterns
          embedded = embeddedSettings
          GameSettings.rules = setupSettings.rules
          validation = setupSettings.validation
          scriptFolders = setupSettings.scriptFolders
          modFilter = setupSettings.modFilter
          initialLookup = STLLookup()
          maxFileSize = setupSettings.maxFileSize
          enableInlineScripts = true }

    do
        if scopeManager.Initialized |> not then
            Utils.logError (sprintf "%A has no scopes" (settings.rootDirectories |> Array.head))
        else
            ()

    let locSettings =
        settings.embedded.localisationCommands
        |> function
            | Legacy(l, v, links) ->
                (if l.Length = 0 then
                     Legacy([], [], [])
                 else
                     Legacy(l, v, links))
            | _ -> Legacy([], [], [])

    let settings =
        { settings with
            embedded =
                { settings.embedded with
                    localisationCommands = locSettings }
            initialLookup = STLLookup() }

    let legacyLocDataTypes =
        settings.embedded.localisationCommands
        |> function
            | Legacy(c, v, links) -> (c, v, (links, settings.embedded.eventTargetLinks))
            | _ -> ([], [], ([], []))

    let processLocalisationFunction lookup =
        (createLocalisationFunctions STL.locStaticSettings createLocDynamicSettings legacyLocDataTypes lookup)

    let mutable dynamicScopeOverride: IClause -> ScopeContext -> ScopeContext option = fun _ _ -> None
    let mutable getActiveInfoService: unit -> InfoService option = fun () -> None
    let mutable carrierResolver: CarrierScopeResolver option = None

    let ensureCarrierResolver resources lookup =
        match carrierResolver with
        | Some resolver -> resolver
        | None ->
            let resolver = CarrierScopeResolver(resources, lookup, fun () -> getActiveInfoService ())
            carrierResolver <- Some resolver
            dynamicScopeOverride <- fun node context -> resolver.Resolve(node, context)
            resolver

    let refreshConfigAfterFirstTypesWithCarrier lookup resources embeddedSettings =
        refreshConfigAfterFirstTypesHook lookup resources embeddedSettings
        ensureCarrierResolver resources lookup |> ignore

    let rulesManagerSettings =
        { rulesSettings = settings.rules
          useFormulas = false
          stellarisScopeTriggers = true
          parseScope = scopeManager.ParseScope()
          allScopes = scopeManager.AllScopes
          anyScope = scopeManager.AnyScope
          scopeGroups = scopeManager.ScopeGroups
          changeScope = changeScope
          scopeContextOverride = fun node context -> dynamicScopeOverride node context
          defaultContext = defaultContext
          defaultLang = STL STLLang.Default
          oneToOneScopesNames = oneToOneScopesNames
          loadConfigRulesHook = loadConfigRulesHook
          refreshConfigBeforeFirstTypesHook = Hooks.refreshConfigBeforeFirstTypesHook
          refreshConfigAfterFirstTypesHook = refreshConfigAfterFirstTypesWithCarrier
          refreshConfigAfterVarDefHook = refreshConfigAfterVarDefHook
          locFunctions = processLocalisationFunction }

    let game =
        GameObject<STLComputedData, STLLookup>.CreateGame
            (settings,
             "stellaris",
             scriptFolders,
             Compute.STL.computeSTLData,
             Compute.STL.computeSTLDataUpdate,
             (STLLocalisationService >> (fun f -> f :> ILocalisationAPICreator)),
             processLocalisationFunction,
             defaultContext,
             noneContext,
             Encoding.UTF8,
             Encoding.GetEncoding(1252),
             validationSettings,
             STLGameFunctions.globalLocalisation,
             STLGameFunctions.afterUpdateFile,
             ".yml",
             rulesManagerSettings,
             setupSettings.debugSettings)
            afterInit

    let carrierScopeResolver = ensureCarrierResolver game.Resources game.Lookup
    do
        getActiveInfoService <- fun () -> game.InfoService
        carrierScopeResolver.Invalidate()

    let lookup = game.Lookup
    let resources = game.Resources
    let fileManager = game.FileManager

    let references =
        References<_>(resources, lookup, game.LocalisationManager.GetCleanLocalisationAPIs())

    let parseErrors () =
        resources.GetResources()
        |> List.choose (function
            | EntityResource(_, e) -> Some e
            | _ -> None)
        |> List.choose (fun r ->
            r.result
            |> function
                | Fail result when r.validate -> Some(r.filepath, result.error, result.position)
                | _ -> None)


    let validateTechnology (entities: (string * Node) list) =
        let tech = entities |> List.filter (fun (f, _) -> f.Contains("common/technology/"))
        tech

    member _.Lookup = lookup

    interface IScopeInferenceProvider with
        member _.ScopeInferenceAtPos pos file _text scopes =
            let rec deepestNode (node: Node) =
                node.Nodes
                |> Seq.tryFind (fun child -> rangeContainsPos child.Position pos)
                |> Option.map deepestNode
                |> Option.defaultValue node

            resources.GetEntityByFilePath file
            |> Option.bind (fun struct (entity, _) ->
                entity.entity.Nodes
                |> Seq.tryFind (fun root -> rangeContainsPos root.Position pos)
                |> Option.map deepestNode)
            |> Option.bind (fun node ->
                let relevant, evidence = carrierScopeResolver.ScopeEvidence node
                if not relevant then
                    None
                else
                    let resolved = scopeManager.GetName scopes.CurrentScope
                    let certainty =
                        if String.Equals(resolved, "Planet", StringComparison.OrdinalIgnoreCase)
                           || String.Equals(resolved, "Ship", StringComparison.OrdinalIgnoreCase) then
                            "exact"
                        elif String.Equals(resolved, "Carrier", StringComparison.OrdinalIgnoreCase) then
                            "union"
                        else
                            "unresolved"

                    Some
                        { kind = "carrier_host"
                          candidates = [ "Planet"; "Ship" ]
                          resolvedScope = resolved
                          certainty = certainty
                          evidence =
                            if evidence.IsEmpty then
                                [ "No unique Planet/Ship caller was found; preserving the Carrier union." ]
                            else
                                evidence })

    interface IGame<STLComputedData> with
        member _.ParserErrors() = parseErrors ()

        member _.ValidationErrors() =
            let s, d = game.ValidationManager.Validate(false, resources.ValidatableEntities()) in s @ d

        member _.LocalisationErrors(force: bool, forceGlobal: bool) =
            getLocalisationErrors game globalLocalisation (force, forceGlobal)

        member _.Folders() = fileManager.AllFolders()
        member _.AllFiles() = resources.GetResources()

        member _.AllLoadedLocalisation() =
            game.LocalisationManager.LocalisationFileNames()

        member _.ScriptedTriggers() = lookup.triggers
        member _.ScriptedEffects() = lookup.effects
        member _.ScriptedVariables() = lookup.scriptedVariables
        member _.StaticModifiers() = lookup.staticModifiers
        member _.UpdateFile shallow file text = game.UpdateFile shallow file text
        member _.UpdateFileInteractive file text = game.UpdateFileInteractive file text
        member _.PrepareUpdateFileInteractive file text = game.PrepareUpdateFileInteractive file text
        member _.CommitUpdateFileInteractive staged = game.CommitUpdateFileInteractive staged
        member _.ValidateFileInteractive staged = game.ValidateFileInteractive staged
        member _.ValidateFile shallow file = game.ValidateFile shallow file
        member _.ValidateFiles files = game.ValidateFiles files
        member _.AllEntities() = resources.AllEntities()

        member _.References() =
            References<_>(resources, lookup, game.LocalisationManager.GetCleanLocalisationAPIs())

        member _.Complete pos file text =
            completion fileManager game.completionService game.InfoService game.ResourceManager pos file text

        member _.ScopesAtPos pos file text =
            scopesAtPos fileManager game.ResourceManager game.InfoService scopeManager.AnyScope pos file text

        member _.GoToType pos file text =
            getInfoAtPos
                fileManager
                game.ResourceManager
                game.InfoService
                game.LocalisationManager
                lookup
                (settings.validation.langs |> Array.tryHead |> Option.defaultValue (STL STLLang.English))
                pos
                file
                text

        member _.FindAllRefs pos file text =
            findAllRefsFromPos fileManager game.ResourceManager game.InfoService pos file text

        member _.FindAllRefsByType typeName id =
            findAllRefsByType game.ResourceManager game.InfoService typeName id

        member _.TypeReferenceIndex() =
            getOrBuildTypeReferenceIndex game.ResourceManager game.InfoService

        member _.InfoAtPos pos file text = game.InfoAtPos pos file text

        member _.OverrideModeAtPath file = game.OverrideModeAtPath file

        member _.OverrideModes() = game.OverrideModes()

        member _.OverrideModesInfo() = game.OverrideModesInfo()

        member _.ReplaceConfigRules rules =
            let result =
                game.ReplaceConfigRules
                    { ruleFiles = rules
                      validateRules = true
                      debugRulesOnly = false
                      debugMode = false } //refreshRuleCaches game (Some { ruleFiles = rules; validateRules = true; debugRulesOnly = false; debugMode = false})
            carrierScopeResolver.Invalidate()
            result

        member _.RefreshCaches() =
            game.RefreshCaches()
            carrierScopeResolver.Invalidate()

        member _.PrepareRefreshCaches() = game.PrepareRefreshCaches()

        member _.CommitRefreshCaches(staged) =
            let committed = game.CommitRefreshCaches(staged)
            if committed then carrierScopeResolver.Invalidate()
            committed

        member _.RefreshScriptedTypes files =
            let typeKeys = incrementalTypeKeysForFiles game files
            if typeKeys.IsEmpty then false
            else
                game.RefreshScriptedTypesForFiles(files, typeKeys)
                carrierScopeResolver.Invalidate()
                true

        member _.RemoveScriptedTypes files =
            let typeKeys = incrementalTypeKeysForFiles game files
            if typeKeys.IsEmpty then false
            else
                for file in files do
                    game.RemoveFile file |> ignore
                game.RefreshScriptedTypesForFiles(files, typeKeys)
                carrierScopeResolver.Invalidate()
                true

        member _.PrepareScriptedTypes(files, additionalSemanticChanged) =
            let typeKeys = incrementalTypeKeysForFiles game files
            if typeKeys.IsEmpty then None
            else game.PrepareScriptedTypesForFiles(files, typeKeys, additionalSemanticChanged)

        member _.CommitScriptedTypes staged =
            let committed = game.CommitScriptedTypesForFiles staged
            if committed && staged.semanticChanged then carrierScopeResolver.Invalidate()
            committed

        member _.RefreshLocalisationCaches() =
            game.LocalisationManager.UpdateProcessedLocalisation()

        member _.CleanupCache(existingFiles) = game.CleanupCache existingFiles
        member _.InvalidateFileCache(filepath) = game.InvalidateFileCache filepath

        member _.ForceRecompute() = resources.ForceRecompute()
        member _.ForceDynamicParameterData(timeoutMs, maxEntities) =
            resources.ForceDynamicParameterData(timeoutMs, maxEntities)
        member _.GetInlineScriptCallers scriptName = resources.GetInlineScriptCallers scriptName
        member _.RefreshInlineScriptCallers scriptNames = game.RefreshInlineScriptCallers scriptNames
        member _.Types() = game.Lookup.typeDefInfo
        member _.TypeDefs() = game.Lookup.typeDefs

        member _.GetPossibleCodeEdits file text =
            getPreTriggerPossible fileManager game.ResourceManager file text

        member _.GetCodeEdits file text =
            getFastTrigger fileManager game.ResourceManager file text

        member _.GetEventGraphData: GraphDataRequest =
            (fun files gameType depth ->
                graphEventDataForFiles references game.ResourceManager lookup files gameType depth)

        member _.GetEmbeddedMetadata() =
            getEmbeddedMetadata lookup game.LocalisationManager game.ResourceManager

    interface IIncrementalTypeIndex with
        member _.PrepareTypeIndex files =
            let typeKeys = incrementalTypeKeysForFiles game files
            game.PrepareTypeIndexForFiles(files, typeKeys)

        member _.CommitTypeIndex staged = game.CommitTypeIndexForFiles staged

        member _.RemoveTypeIndex files =
            let typeKeys = incrementalTypeKeysForFiles game files
            if typeKeys.IsEmpty then false
            else game.RemoveTypeIndexForFiles(files, typeKeys)

    interface IIncrementalLocalisation with
        member _.TakeLocalisationDelta() =
            let delta = game.LocalisationManager.TakeDelta()
            if game.LocalisationManager.localisationErrors.IsSome
               && game.LocalisationManager.globalLocalisationErrors.IsSome then
                delta
            else
                None
        member _.ValidateLocalisationDelta delta = validateIncrementalLocalisation game delta
        member _.ValidateLocalisationFiles files = validateIncrementalLocalisationFiles game [||] files

    interface ISemanticDeltaProvider with
        member _.SemanticSignatureForFile filepath =
            semanticSignatureForFile game filepath

    interface ICancellableFileValidation with
        member _.ValidateFileInteractiveCancellable(staged, shouldCancel) =
            game.ValidateFileInteractiveCancellable staged shouldCancel

        member _.ValidateFileCancellable(shallow, file, shouldCancel) =
            game.ValidateFileCancellable shallow file shouldCancel
