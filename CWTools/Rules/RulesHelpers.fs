module CWTools.Rules.RulesHelpers

open System
open System.Collections.Generic
open System.Collections.Frozen
open System.IO
open CSharpHelpers
open CWTools.Games
open CWTools.Process
open CWTools.Rules.RulesWrapper
open CWTools.Utilities
open CWTools.Utilities.Utils2
open FSharp.Collections.ParallelSeq
open CWTools.Utilities.Utils
open CWTools.Common

let private tryDefinitionInjectionKey (key: string) =
    let index = key.IndexOf(':')

    if index <= 0 || index >= key.Length - 1 then
        None
    else
        let mode = key.Substring(0, index).ToUpperInvariant()
        let target = key.Substring(index + 1)

        match mode with
        | "INJECT"
        | "REPLACE"
        | "TRY_INJECT"
        | "TRY_REPLACE"
        | "INJECT_OR_CREATE"
        | "REPLACE_OR_CREATE" -> Some(mode, target)
        | _ -> None

let private isDefinitionInjectionCreateMode mode =
    mode = "REPLACE_OR_CREATE"


let getTypesFromDefinitions
    (ruleapplicator: RuleValidationService option)
    (types: TypeDefinition list)
    (entities: Entity seq)
    =
    let getExplicitLocalisationKeys (entity: IClause) (typeDef: TypeDefinition) =
        typeDef.localisation
        |> List.choose (fun ld -> ld.explicitField |> Option.map (fun ef -> ld.name, ef, ld.primary))
        |> List.choose (fun (name, field, primary) ->
            entity.Tag field |> Option.map (fun v -> name, v.ToRawString(), primary))

    let getTypeInfo (def: TypeDefinition) =
        entities
        |> Seq.choose (fun e ->
            if CSharpHelpers.FieldValidatorsHelper.CheckPathDir(def.pathOptions, e.logicalpath) then
                Some(e.entity, Path.GetFileNameWithoutExtension e.logicalpath, e.validate)
            else
                None)
        |> Seq.collect (fun (e, fileNameWithoutExtension, v) ->
            let inner (n: IClause) =
                let rawSubtypes, subtypes =
                    match ruleapplicator with
                    | Some ruleapplicator ->
                        let rawSubtypes = ruleapplicator.TestSubType(def.subtypes, n) |> snd
                        rawSubtypes, rawSubtypes |> List.map (fun s -> def.name + "." + s)
                    | None -> [], []

                let filterKey =
                    match n with
                    | :? ValueClause as vc -> vc.FirstKey |> Option.defaultValue "clause"
                    | _ -> n.Key

                let prefixKey =
                    match n with
                    | :? Node as n -> n.KeyPrefix
                    | _ -> None

                let key =
                    match def.nameField with
                    | Some f -> n.TagText f
                    | None ->
                        match n with
                        | :? ValueClause as vc -> vc.SecondKey |> Option.defaultValue "clause"
                        | _ ->
                            match tryDefinitionInjectionKey n.Key with
                            | Some(mode, target) when isDefinitionInjectionCreateMode mode -> target
                            | _ -> n.Key

                let result =
                    match tryDefinitionInjectionKey filterKey with
                    | Some(mode, _) when not (isDefinitionInjectionCreateMode mode) -> []
                    | _ ->
                        def.name :: subtypes
                        |> List.map (fun s -> s, (v, key, n.Position, getExplicitLocalisationKeys n def, rawSubtypes))

                if FieldValidators.typekeyfilter def filterKey prefixKey then
                    result
                else
                    []

            let childres =
                let rec skiprootkey (srk: SkipRootKey list) (n: IClause) =
                    let childKey =
                        match n with
                        | :? ValueClause as vc ->
                            vc.FirstKey |> Option.orElse vc.SecondKey |> Option.defaultValue "clause"
                        | _ -> n.Key

                    match srk with
                    | [] -> []
                    | [ SpecificKey key ] ->
                        //Too may levels deep
                        if childKey == key then
                            n.ClauseList |> List.collect inner
                        else
                            []
                    | [ AnyKey ] -> n.ClauseList |> List.collect inner
                    | MultipleKeys(keys, shouldMatch) :: _ ->
                        if (keys |> List.exists ((==) childKey)) <> (not shouldMatch) then
                            n.ClauseList |> List.collect inner
                        else
                            []
                    | SpecificKey key :: tail ->
                        if childKey == key then
                            n.ClauseList |> List.collect (skiprootkey tail)
                        else
                            []
                    | AnyKey :: tail -> n.ClauseList |> List.collect (skiprootkey tail)

                match def.type_per_file, def.skipRootKey with
                | true, _ ->
                    let rawSubtypes, subtypes =
                        match ruleapplicator with
                        | Some ruleapplicator ->
                            let rawSubtypes = ruleapplicator.TestSubType(def.subtypes, e) |> snd
                            let subtypes = rawSubtypes |> List.map (fun s -> def.name + "." + s)
                            rawSubtypes, subtypes
                        | None -> [], []

                    def.name :: subtypes
                    |> List.map (fun s ->
                        s, (v, fileNameWithoutExtension, e.Position, getExplicitLocalisationKeys e def, rawSubtypes))
                | false, [] -> (e.Clauses |> List.ofSeq |> List.collect inner)
                | false, srk -> e.Clauses |> List.ofSeq |> List.collect (skiprootkey srk)

            childres
            @ (e.LeafValues
               |> List.ofSeq
               |> List.map (fun lv -> def.name, (v, lv.Value.ToString(), lv.Position, [], []))))

    let resDict = Dictionary<string, _>()

    types
    |> PSeq.collect getTypeInfo
    |> Seq.iter (fun (n, k) ->
        let mutable value: (bool * string * Position.range * (string * string * bool) list * string list) list =
            Unchecked.defaultof<_>

        if resDict.TryGetValue(n, &value) then
            resDict[n] <- k :: value
        else
            resDict[n] <- [ k ])

    types
    |> List.iter (fun typeDefinition ->
        if resDict.ContainsKey typeDefinition.name then
            ()
        else
            resDict[typeDefinition.name] <- [])

    resDict
    |> Seq.map (fun kv ->
        let k = kv.Key
        let vs = kv.Value

        k,
        vs
        |> Seq.map (fun (v, n, r, el, sts) ->
            { TypeDefInfo.validate = v
              id = n
              range = r
              explicitLocalisation = el
              subtypes = sts }) |> Seq.toArray)
    |> Map.ofSeq

let getEnumsFromComplexEnums (complexenums: ComplexEnumDef list) (es: Entity seq) : EnumDefinition list =
    let entities = es |> Seq.toArray
    let scalarKeyId = StringResource.stringManager.InternIdentifierToken "scalar"
    let enumNameKeyId = StringResource.stringManager.InternIdentifierToken "enum_name"
    let nameKeyId = StringResource.stringManager.InternIdentifierToken "name"

    let rec inner (enumtree: Node) (node: Node) =
        // log (sprintf "gece %A %A %A" (node.ToRaw) (enumtree.ToRaw) (node.Position.FileName))
        // log (sprintf "gecee %A %A" enumtree.Key node.Key)
        let childRes =
            let einner (enumtreeNode: Node) =
                let key = enumtreeNode.KeyId

                let isScalar =
                    key.lower = scalarKeyId.lower
                    || key.lower = enumNameKeyId.lower
                    || key.lower = nameKeyId.lower
                // log (sprintf "gecee2 %A %A %A" enumtreeNode.Key node.Key isScalar)

                let enumnameRes =
                    if key.lower = enumNameKeyId.lower then
                        node.Nodes |> Seq.map (fun n -> n.Key.Trim('\"'), Some n.Position)
                    else
                        Seq.empty

                let innerRes =
                    if isScalar then
                        node.Nodes |> Seq.collect (inner enumtreeNode)
                    else
                        node.Nodes
                        |> Seq.filter (fun c -> c.KeyId.lower = key.lower)
                        |> Seq.collect (inner enumtreeNode)

                seq {
                    yield! enumnameRes
                    yield! innerRes
                }

            enumtree.Nodes |> Seq.collect einner
        // match enumtree.Children with
        // |head::_ ->
        //     let keyRes =
        //         if enumtree.Children |> List.exists (fun n -> n.Key == "enum_name")
        //         then node.Children |> List.map (fun n -> n.Key.Trim([|'\"'|])) else []
        //     keyRes @ (node.Children |> List.collect (inner head))
        // // TODO: Also check Leaves/leafvalues here when both are defined
        // |[] -> []
        let leafValueRes =
            if
                enumtree.LeafValues
                |> Seq.exists (fun lv -> lv.ValueId.lower = enumNameKeyId.lower)
            then
                node.LeafValues |> Seq.map (fun lv -> lv.ValueText.Trim('\"'), Some lv.Position)
            else
                Seq.empty

        let leafRes =
            match enumtree.Leaves |> Seq.tryFind (fun l -> l.ValueId.lower = enumNameKeyId.lower) with
            | Some leaf ->
                let k = leaf.Key
                // log (sprintf "gecel %A %A" k node.Leaves)
                if k == "scalar" then
                    node.Leaves |> Seq.map (fun l -> l.ValueText.Trim('\"'), Some l.Position)
                else
                    node.TagsText k |> Seq.map (fun k -> k.Trim('\"'), None)
            | None ->
                match enumtree.Leaves |> Seq.tryFind (fun l -> l.KeyId.lower = enumNameKeyId.lower) with
                | Some leaf ->
                    let vt = leaf.ValueText
                    // log (sprintf "gecel %A %A" vt node.Leaves)
                    if vt == "scalar" then
                        node.Leaves |> Seq.map (fun l -> l.Key.Trim('\"'), Some l.Position)
                    else
                        node.Leaves
                        |> Seq.choose (fun l ->
                            if l.ValueText == vt then
                                Some(l.Key.Trim('\"'), Some l.Position)
                            else
                                None)
                | None -> Seq.empty

        seq {
            yield! childRes
            yield! leafValueRes
            yield! leafRes
        }

    let innerStart (enumtree: Node) (node: Node) = inner enumtree node
    //enumtree.Children |> List.collect (fun e -> node.Children |> List.collect (inner e ))
    let getEnumInfo (complexenum: ComplexEnumDef) =
        let values =
            entities
            |> Seq.choose (fun e ->
                if CSharpHelpers.FieldValidatorsHelper.CheckPathDir(complexenum.pathOptions, e.logicalpath) then
                    Some e.entity
                else
                    None)
            |> Seq.collect (fun e ->
                if complexenum.start_from_root then
                    innerStart complexenum.nameTree e
                else
                    e.Nodes |> Seq.collect (innerStart complexenum.nameTree))
            |> Seq.toArray
        // log "%A %A" complexenum.name values
        { key = complexenum.name
          values = values |> Array.map fst
          description = complexenum.description
          valuesWithRange = values }

    complexenums
    |> List.toSeq
    |> PSeq.map getEnumInfo
    |> Seq.fold
        (fun acc e ->
            if Map.containsKey e.key acc then
                Map.add
                    e.key
                    { e with
                        values = Array.append e.values acc[e.key].values
                        valuesWithRange = Array.append e.valuesWithRange acc[e.key].valuesWithRange }
                    acc
            else
                Map.add e.key e acc)
        Map.empty
    |> Map.toList
    |> List.map snd

let expandPredefinedValues
    (types: Map<string, PrefixOptimisedStringSet>)
    (enums: Map<string, _ * array<string * option<Position.range>>>)
    (values: string list)
    =
    let replaceType (value: string) =
        let startIndex = value.IndexOf "<"
        let endIndex = value.IndexOf ">" - 1
        let referencedType = value.Substring(startIndex + 1, (endIndex - startIndex))

        match types |> Map.tryFind referencedType with
        | Some typeValues ->
            // eprintfn "epv %A %A %A %A" value typeValues (value.Substring(0, startIndex)) (value.Substring(endIndex + 2))
            let res =
                typeValues.StringValues
                |> Seq.map (fun tv -> value.Substring(0, startIndex) + tv + value.Substring(endIndex + 2))
                |> List.ofSeq
            // eprintfn "epv2 %A" res
            res
        | None -> [ value ]

    let replaceEnum (value: string) =
        let startIndex = value.IndexOf "enum["
        let endIndex = value.IndexOf "]" - 1
        let referencedEnum = value.Substring(startIndex + 5, (endIndex - (startIndex + 4)))

        match enums |> Map.tryFind referencedEnum with
        | Some(_, enumValues) ->
            let res =
                enumValues
                |> Seq.map (
                    fst
                    >> (fun tv -> value.Substring(0, startIndex) + tv + value.Substring(endIndex + 2))
                )
                |> List.ofSeq
            // eprintfn "epv2 %A" res
            res
        | None -> [ value ]

    values
    |> List.collect (fun v ->
        if v.Contains "<" && v.Contains ">" then
            replaceType v
        else
            [ v ])
    |> List.collect (fun v ->
        if v.Contains "enum[" && v.Contains "]" then
            replaceEnum v
        else
            [ v ])

// let generateModifiersFromType (typedefs : TypeDefinition list) (invertedTypeMap : Collections.Map<string, TypeDefInfo list>) (typeKey : string) (key : string) =
//     let typenames = typeKey.Split('.')
//     let typename = typenames.[0]
//     let actualSubtypes =
//         match invertedTypeMap |> Map.tryFind key with
//         | Some keytypes ->
//             keytypes |> List.tryPick (fun kt -> if kt.id = key kt.subtypes)
//             // keytypes |> List.filter (fun kt -> kt.StartsWith (typename+".", StringComparison.OrdinalIgnoreCase))
//                      // |> List.map (fun kt -> kt.Split('.').[1])
//         | None -> []
//     match typedefs |> List.tryFind (fun t -> t.name == typename) with
//     |None -> []
//     |Some typedef ->
//         let inner =
//             (fun (l : TypeModifier) ->
//             let modifierKey = l.prefix + key + l.suffix
//             { ActualModifier.tag = modifierKey
//               source = ModifierSource.TypeDef (key, typedef.name)
//               category = l.category
//               })
//         let subtype =
//             let subtypes = (if typenames.Length > 1 then typenames.[1]::actualSubtypes else actualSubtypes) |> List.distinct
//             let inner2 (nextSt : string) =
//                 match typedef.subtypes |> List.tryFind (fun st -> st.name == nextSt) with
//                 |None -> []
//                 |Some st -> st.modifiers |> List.map inner
//             subtypes |> List.collect inner2
//         (typedef.modifiers |> List.map inner) @ subtype
let generateModifiersFromType (typedef: TypeDefinition) (typeInstance: TypeDefInfo) =
    let actualSubtypes = typeInstance.subtypes

    let inner =
        (fun (l: TypeModifier) ->
            let modifierKey = l.prefix + typeInstance.id + l.suffix

            { ActualModifier.tag = modifierKey
              // source = ModifierSource.TypeDef (typeInstance.id, typedef.name)
              category = l.category })

    let subtype =
        let inner2 (nextSt: string) =
            match typedef.subtypes |> List.tryFind (fun st -> st.name == nextSt) with
            | None -> []
            | Some st -> st.modifiers |> List.map inner

        actualSubtypes |> List.collect inner2

    (typedef.modifiers |> List.map inner) @ subtype

let generateModifiersFromTypes (typedefs: TypeDefinition list) (typeDefMap: Collections.Map<string, TypeDefInfo array>) =
    typedefs
    |> List.collect (fun td ->
        match typeDefMap |> Map.tryFind td.name with
        | Some typeInstances -> typeInstances |> Seq.collect (fun ti -> generateModifiersFromType td ti) |> List.ofSeq
        | None -> [])

let private modifierRuleFromNameAndTypeDef (nameWithSubtypes: string) (m: TypeModifier) =
    let modifierOptions =
        { Options.DefaultOptions with
            requiredScopes = modifierCategoryManager.SupportedScopes m.category
            typeHint = Some("modifier_type", false) }

    let lhs =
        if m.prefix = "" && m.suffix = "" then
            TypeField(TypeType.Simple(nameWithSubtypes))
        else
            TypeField(TypeType.Complex(m.prefix, nameWithSubtypes, m.suffix))

    AliasRule("modifier", NewRule(LeafRule(lhs, ValueField(ValueType.Float(RulesParserConstants.floatFieldDefaultMinimum, RulesParserConstants.floatFieldDefaultMaximum))), modifierOptions))

let generateModifierRulesFromTypes (typedefs: TypeDefinition list) =
    typedefs
    |> List.collect (fun td ->
        td.modifiers
        |> List.map (fun m -> modifierRuleFromNameAndTypeDef td.name m)
        |> List.append (
            td.subtypes
            |> List.collect (fun st ->
                st.modifiers
                |> List.map (fun m -> modifierRuleFromNameAndTypeDef (td.name + "." + st.name) m))
        ))

/// Alias-key completion map shared by RuleValidationService/InfoService/CompletionService.
/// The three services previously each computed an identical copy in their constructors;
/// computing it once per service rebuild and passing it in cuts that to a single pass.
let computeAliasKeyMap
    (rootRules: RulesWrapper)
    (types: FrozenDictionary<string, PrefixOptimisedStringSet>)
    (enums: FrozenDictionary<string, string * PrefixOptimisedStringSet>)
    : Map<string, HashSet<StringToken>> =
    let ruleToCompletionListHelper =
        function
        | LeafRule(SpecificField(SpecificValue x), _), _ -> seq { yield x.lower }
        | NodeRule(SpecificField(SpecificValue x), _), _ -> seq { yield x.lower }
        | LeafRule(NewField.TypeField(TypeType.Simple t), _), _
        | NodeRule(NewField.TypeField(TypeType.Simple t), _), _ ->
            types.TryFind(t)
            |> Option.map (fun s -> s.IdValues |> Seq.map _.lower)
            |> Option.defaultValue Seq.empty
        | LeafRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _
        | NodeRule(NewField.TypeField(TypeType.Complex(p, t, suff)), _), _ ->
            types.TryFind(t)
            |> Option.map (fun s ->
                s.IdValues
                |> Seq.map (fun i ->
                    let s = StringResource.stringManager.GetStringForID i.normal
                    StringResource.stringManager.InternIdentifierToken(p + s + suff).lower))
            |> Option.defaultValue Seq.empty
        | LeafRule(NewField.ValueField(Enum e), _), _
        | NodeRule(NewField.ValueField(Enum e), _), _ ->
            enums.TryFind(e)
            |> Option.map (fun (_, s) -> s.IdValues |> Seq.map _.lower)
            |> Option.defaultValue Seq.empty
        | _ -> Seq.empty

    rootRules.Aliases
    |> Map.toList
    |> List.map (fun (key, rules) -> key, (rules |> Seq.collect ruleToCompletionListHelper |> HashSet<StringToken>))
    |> Map.ofList
