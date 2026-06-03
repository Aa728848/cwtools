namespace CWTools.Validation.Stellaris

open CWTools.Validation
open CWTools.Validation.ValidationCore
open CWTools.Process
open CWTools.Parser.Types
open CWTools.Common
open CWTools.Common.STLConstants
open CWTools.Games
open CWTools.Utilities.Utils
open System
open FSharpx.Collections


module Graphics =

    let inline validateEntityCulture
        (entities: Collections.Set<string>)
        (cultures: (string * string list) list)
        (entity: string)
        leaf
        (culture: string)
        =
        let secondKey =
            cultures
            |> List.tryPick (fun (c, f) -> if c == culture then Some f else None)
            |> Option.defaultValue []
        //|> Option.map (fun k -> k + "_" + entity)
        let firstkey = culture + "_" + entity

        let res =
            secondKey
            |> List.fold
                (fun (s: string option) c ->
                    if s.IsNone || entities.Contains(c + "_" + entity) then
                        None
                    else
                        Some c)
                (Some firstkey)

        match (entities.Contains entity) || (entities.Contains firstkey), res with
        | true, _ -> None
        | false, None -> None
        //Some (Invalid (Guid.NewGuid(), [inv (ErrorCodes.UndefinedSectionEntity firstkey culture) leaf]))
        | false, Some fallback ->
            if entities.Contains fallback then
                None
            else
                Some(
                    Invalid(
                        Guid.NewGuid(),
                        [ inv (ErrorCodes.UndefinedSectionEntityFallback firstkey fallback culture) leaf ]
                    )
                )

    let inline validateEntityCultures
        (entities: Collections.Set<string>)
        (allcultures: (string * string list) list)
        (entity: string)
        leaf
        (cultures: string list)
        =
        let errors =
            cultures |> List.choose (validateEntityCulture entities allcultures entity leaf)

        match errors with
        | [] -> OK
        | [ x ] -> x
        | [ x1; x2 ] -> x1 <&&> x2
        | x1 :: x2 :: _ ->
            x1
            <&&> x2
            <&&> (Invalid(Guid.NewGuid(), [ inv (ErrorCodes.CustomError "and more errors hidden" Severity.Error) leaf ]))


    let getGraphicalCultures (es: STLEntitySet) =
        es.AllOfTypeChildren EntityType.GraphicalCulture
        |> List.map (fun c -> c.Key, c.TagText "fallback")

    let getGraphicalCultureRefs (node: Node) =
        node.Childs "graphical_culture"
        |> Seq.collect (fun gc -> gc.LeafValues |> Seq.map (fun lv -> lv.Value.ToRawString()))
        |> List.ofSeq

    let isGraphicalCultureDisabled (node: Node) =
        node.Leafs "graphical_culture"
        |> Seq.exists (fun gc ->
            String.Equals(gc.Value.ToRawString().Trim('"'), "no", StringComparison.OrdinalIgnoreCase))

    let getGraphicalCultureSearchList (allCultures: string list) (node: Node) =
        if isGraphicalCultureDisabled node then
            []
        else
            match getGraphicalCultureRefs node with
            | [] -> allCultures
            | cultures -> cultures

    let validateEntityWithGraphicalCultures
        (assets: Collections.Set<string>)
        (cultureFallbacks: (string * string list) list)
        (allowedCultures: string list)
        (entity: string)
        target
        =
        if assets.Contains entity then
            OK
        elif
            allowedCultures
            |> List.exists (fun culture ->
                validateEntityCulture assets cultureFallbacks entity target culture |> Option.isNone)
        then
            OK
        else
            Invalid(Guid.NewGuid(), [ inv (ErrorCodes.UndefinedEntity entity) target ])

    let valSectionGraphics: STLStructureValidator =
        fun os es ->
            let cultures =
                (getGraphicalCultures os @ getGraphicalCultures es)
                |> List.distinctBy fst

            let cultureMap = cultures |> List.filter (fun (_, f) -> f <> "") |> Map.ofList

            let cultures =
                cultures
                |> List.map (fun (c, f) ->
                    c,
                    Seq.unfold (fun nc -> cultureMap.TryFind nc |> Option.map (fun nf -> nf, nf)) c
                    |> List.ofSeq)

            let allCultures = cultures |> List.map fst

            let shipsizesV =
                es.AllOfTypeChildren EntityType.ShipSizes
                |> List.filter (fun ss -> not (ss.Has "entity"))
                |> List.map (fun ss -> ss, ss.Key, getGraphicalCultureSearchList allCultures ss)

            let assets =
                (os.AllOfTypeChildren EntityType.GfxAsset @ es.AllOfTypeChildren EntityType.GfxAsset)
                |> List.map (fun a -> a.TagText "name")
                |> Set.ofList

            shipsizesV
            <&!&> (fun (ss, n, c) -> validateEntityWithGraphicalCultures assets cultures c (n + "_entity") ss)

    let valComponentGraphics: STLStructureValidator =
        fun os es ->
            let components =
                es.AllOfTypeChildren EntityType.ComponentTemplates
                |> List.filter (fun c ->
                    (c.Tag "hidden")
                    |> Option.bind (function
                        | Value.Bool x -> Some(not x)
                        | _ -> Some true)
                    |> Option.defaultValue true)

            let cultures = getGraphicalCultures os
            let cultureMap = cultures |> List.filter (fun (_, f) -> f <> "") |> Map.ofList

            let cultures =
                cultures
                |> List.map (fun (c, f) ->
                    c,
                    Seq.unfold (fun nc -> cultureMap.TryFind nc |> Option.map (fun nf -> nf, nf)) c
                    |> List.ofSeq)
            // let assets = os.AllOfTypeChildren EntityType.GfxAsset
            //                 |> List.map (fun a -> a.TagText "name")
            //                 |> Set.ofList
            let assetGenerator (e: Entity) : obj list =
                if e.entityType = EntityType.GfxAsset then
                    e.entity.Children |> List.map (fun a -> upcast a.TagText "name")
                else
                    []

            let assets =
                os.AddOrGetCached "componentgraphicsassets" assetGenerator
                |> List.map (fun s -> s :?> string)
                |> Set.ofList

            let inner =
                fun (s: Node) ->
                    match s.Leafs "entity" |> Seq.tryHead with
                    | None -> OK
                    | Some entity ->
                        (cultures |> List.map fst)
                        |> validateEntityCultures assets cultures (s.TagText "entity") entity

            components <&!&> inner

    let valMegastructureGraphics: STLStructureValidator =
        fun os es ->
            let megastructures = es.AllOfTypeChildren EntityType.Megastructures
            //|> List.collect (fun a -> a.Leafs "entity" |> List.ofSeq)
            let cultures = getGraphicalCultures os
            let cultureMap = cultures |> List.filter (fun (_, f) -> f <> "") |> Map.ofList

            let cultures =
                cultures
                |> List.map (fun (c, f) ->
                    c,
                    Seq.unfold (fun nc -> cultureMap.TryFind nc |> Option.map (fun nf -> nf, nf)) c
                    |> List.ofSeq)

            let assets =
                os.AllOfTypeChildren EntityType.GfxAsset
                |> List.map (fun a -> a.TagText "name")
                |> Set.ofList

            let inner =
                fun (m: Node) ->
                    let check =
                        fun (e: Leaf) ->
                            (cultures |> List.map fst)
                            |> validateEntityCultures assets cultures (e.Value.ToRawString()) m

                    m.Leafs "entity" <&!&> check <&&> (m.Leafs "construction_entity" <&!&> check)

            megastructures <&!&> inner

    let valPlanetClassGraphics: STLStructureValidator =
        fun os es ->
            let assets =
                os.AllOfTypeChildren EntityType.GfxAsset
                |> List.map (fun a -> a.TagText "name")
                |> Set.ofList

            es.AllOfTypeChildren EntityType.PlanetClasses
            |> List.collect (fun ao -> ao.Leafs "entity" |> List.ofSeq)
            <&!&> (fun l ->
                if
                    assets.Contains(l.Value.ToRawString())
                    || assets.Contains(l.Value.ToRawString() + "_01_entity")
                then
                    OK
                else
                    Invalid(Guid.NewGuid(), [ inv (ErrorCodes.UndefinedEntity(l.Value.ToRawString())) l ]))
