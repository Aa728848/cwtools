namespace CWTools.Rules

open System.Collections.Frozen
open System.Collections.Generic
open System.Linq
open CSharpHelpers
open CWTools.Common
open CWTools.Process.Scopes
open CWTools.Utilities.Utils2
open CWTools.Utilities
open CWTools.Utilities.Utils
open CWTools.Utilities.StringResource
open CWTools.Process.Localisation
open Cysharp.Text

type RuleContext =
    { subtypes: string list
      scopes: ScopeContext
      warningOnly: bool }

type CheckFieldParams =
    { varMap: FrozenDictionary<string, PrefixOptimisedStringSet>
      enumsMap: FrozenDictionary<string, string * PrefixOptimisedStringSet>
      typesMap: FrozenDictionary<string, PrefixOptimisedStringSet>
      databaseObjectTypes: Map<string, DatabaseObjectTypeConfig>
      linkMap: EffectMap
      wildcardLinks: ScopedEffect list
      valueTriggerMap: EffectMap
      varSet: PrefixOptimisedStringSet
      localisation: (Lang * Collections.Set<string>) array
      defaultLocalisation: Collections.Set<string>
      files: FrozenSet<string>
      changeScope: ChangeScope
      anyScope: Scope
      defaultLang: Lang
      aliasKeys: Map<string, HashSet<StringToken>>
      processLocalisation: Lang * Map<string, CWTools.Localisation.Entry> -> Lang * Map<string, LocEntry>
      validateLocalisation: LocEntry -> ScopeContext -> CWTools.Validation.ValidationResult }

[<RequireQualifiedAccess>]
module internal FieldValidators =

    open System
    open System.Text.RegularExpressions
    open CWTools.Process
    open CWTools.Validation
    open CWTools.Validation.ValidationCore
    open CWTools.Rules

    [<Literal>]
    let CK2DnaLength = 11

    let getValidValues =
        function
        | ValueType.Bool -> Some [| "yes"; "no" |]
        | ValueType.Enum es -> Some [| es |]
        | _ -> None

    // type ScopeContext = IScopeContext<Scope>

    // type RuleContext  = RuleContext<Scope>
    let firstCharEqualsAmp (key: StringToken) =
        (stringManager.GetMetadataForID key).startsWithAmp

    /// Check if the string value contains an embedded @variable reference
    /// (e.g., "prefix_@var_suffix"), indicating an unresolved scripted variable
    /// that can only be evaluated at runtime.
    let containsEmbeddedAtVariable (s: string) =
        let mutable i = 0
        let mutable found = false
        while i < s.Length - 1 && not found do
            if s.[i] = '@' && (Char.IsLetter(s.[i + 1]) || s.[i + 1] = '_') then
                found <- true
            i <- i + 1
        found

    let getStringMetadata (key: StringToken) = (stringManager.GetMetadataForID key)
    // let firstCharEqualsAmp (s : string) = s.Length > 0 && (s.[0] = '@')// || s.[0] = '$')
    let inline trimQuote (s: string) = s.Trim('\"')
    let inline trimQuoteSpan (s: string) = s.AsSpan().Trim('\"')
    let inline getLowerKey (ids: StringTokens) = stringManager.GetLowerStringForIDs(ids)
    let inline getOriginalKey (ids: StringTokens) = stringManager.GetStringForIDs ids

    let stripPrefixedValueText (value: string) =
        let value = trimQuote value
        let colonIndex = value.IndexOf(':')

        if colonIndex > 0 && colonIndex + 1 < value.Length && value.[colonIndex + 1] <> '\\' && value.[colonIndex + 1] <> '/' then
            value.Substring(colonIndex + 1)
        else
            value

    let stripPrefixedValueIds (ids: StringTokens) =
        getOriginalKey ids
        |> stripPrefixedValueText
        |> stringManager.InternIdentifierToken

    let private tryResolveScopedTriggerValue
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        varSet
        (changeScope: ChangeScope)
        (scope: ScopeContext)
        (key: ReadOnlySpan<char>)
        =
        let key = key.ToString()
        let marker = ".trigger:"
        let markerIndex = key.IndexOf(marker, StringComparison.OrdinalIgnoreCase)

        if markerIndex < 0 then
            None
        else
            let scopePath = key.Substring(0, markerIndex)
            let triggerName = key.Substring(markerIndex + marker.Length)

            if String.IsNullOrWhiteSpace triggerName || triggerName.IndexOf('$') >= 0 then
                None
            else
                let scopedContextResult =
                    if String.IsNullOrWhiteSpace scopePath then
                        Some(Choice1Of2 scope)
                    else
                        match
                            changeScope.Invoke(
                                false,
                                true,
                                linkMap,
                                valueTriggerMap,
                                wildcardLinks,
                                varSet,
                                scopePath.AsSpan(),
                                scope
                            )
                        with
                        | ScopeResult.NewScope(newScope, _, _) -> Some(Choice1Of2 newScope)
                        | ScopeResult.WrongScope _ as result -> Some(Choice2Of2 result)
                        | ScopeResult.VarNotFound _ as result -> Some(Choice2Of2 result)
                        | _ -> None

                match scopedContextResult with
                | Some(Choice1Of2 scopedContext) ->
                    match
                        changeScope.Invoke(
                            false,
                            true,
                            linkMap,
                            valueTriggerMap,
                            wildcardLinks,
                            varSet,
                            triggerName.AsSpan(),
                            scopedContext
                        )
                    with
                    | ScopeResult.ValueFound _ as result -> Some result
                    | ScopeResult.WrongScope _ as result -> Some result
                    | ScopeResult.VarNotFound _ as result -> Some result
                    | _ -> None
                | Some(Choice2Of2 result) -> Some result
                | None -> None

    let checkValidValue
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (enumsMap: FrozenDictionary<_, string * PrefixOptimisedStringSet>)
        (keys: (Lang * Collections.Set<string>) array)
        (severity: Severity)
        (vt: ValueType)
        (ids: StringTokens)
        leafornode
        errors
        =
        let key = getLowerKey ids
        let originalKey = getOriginalKey ids

        // Check if it's a @[...] or @\[...] expression - treat as valid numeric value
        if (originalKey.StartsWith("@[") || originalKey.StartsWith(@"@\[")) && originalKey.EndsWith("]") then
            errors
        elif firstCharEqualsAmp ids.lower then
            errors
        else
            match vt with
            | ValueType.Bool ->
                if key == "yes" || key == "no" then
                    errors
                else
                    inv (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting yes or no, got %s{key}" severity) leafornode
                    <&&&> errors
            | ValueType.Int(min, max) ->
                match TryParser.parseInt64WithDecimal key with
                | ValueSome i ->
                    if i <= max && i >= min then
                        errors
                    else
                        inv
                            (ErrorCodes.ConfigRulesUnexpectedValue
                                $"Expecting a value between %i{min} and %i{max}"
                                severity)
                            leafornode
                        <&&&> errors
                | ValueNone ->
                    match enumsMap.TryFind "static_values" with
                    | Some(_, es) ->
                        if es.Contains(trimQuoteSpan key) then
                            errors
                        else
                            inv
                                (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting an integer, got %s{key}" severity)
                                leafornode
                            <&&&> errors
                    | None ->
                        inv
                            (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting an integer, got %s{key}" severity)
                            leafornode
                        <&&&> errors
            | ValueType.Float(min, max) ->
                match TryParser.parseDecimal key with
                | ValueSome f ->
                    if f <= max && f >= min then
                        errors
                    else
                        inv
                            (ErrorCodes.ConfigRulesUnexpectedValue
                                $"Expecting a value between %f{min} and %f{max}"
                                severity)
                            leafornode
                        <&&&> errors
                | ValueNone ->
                    match enumsMap.TryFind "static_values" with
                    | Some(_, es) ->
                        if es.Contains(trimQuoteSpan key) then
                            errors
                        else
                            inv
                                (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting a float, got %s{key}" severity)
                                leafornode
                            <&&&> errors
                    | None ->
                        inv
                            (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting a float, got %s{key}" severity)
                            leafornode
                        <&&&> errors
            | ValueType.Enum e ->
                match enumsMap.TryFind e with
                | Some(desc, es) ->
                    if es.Contains(trimQuoteSpan key) then
                        errors
                    else
                        let defaultValue = "???"

                        inv
                            (ErrorCodes.ConfigRulesUnexpectedValue
                                $"Expecting a \"%s{desc}\" value, e.g. %A{es.StringValues |> Seq.tryHead |> Option.defaultValue defaultValue}"
                                severity)
                            leafornode
                        <&&&> errors
                | None ->
                    inv
                        (ErrorCodes.RulesError
                            $"Configuration error: there are no defined values for the enum %s{e}"
                            severity)
                        leafornode
                    <&&&> errors
            // | ValueType.Specific s ->
            //     // if trimQuote key == s then OK else Invalid (Guid.NewGuid(), [inv (ErrorCodes.ConfigRulesUnexpectedValue (sprintf "Expecting value %s" s) severity) leafornode])
            //     if id = s.lower then errors else inv (ErrorCodes.ConfigRulesUnexpectedValue (sprintf "Expecting value %s" (StringResource.stringManager.GetStringForID(s.normal))) severity) leafornode <&&&> errors
            | ValueType.Percent ->
                if key.EndsWith('%') then
                    errors
                else
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting an percentage, got %s{key}" severity)
                        leafornode
                    <&&&> errors
            | ValueType.Date ->
                let ok = FieldValidatorsHelper.IsValidDate(key)

                if ok then
                    errors
                else
                    inv (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting a date, got %s{key}" severity) leafornode
                    <&&&> errors
            | ValueType.DateTime ->
                let ok = FieldValidatorsHelper.IsValidDateTime(key)

                if ok then
                    errors
                else
                    inv (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting a date, got %s{key}" severity) leafornode
                    <&&&> errors
            | ValueType.CK2DNA ->
                if key.Length = CK2DnaLength && key |> Seq.forall (fun c -> Char.IsLetter c || c = '0') then
                    errors
                else
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting a dna value, got %s{key}" severity)
                        leafornode
                    <&&&> errors
            | ValueType.CK2DNAProperty ->
                if key.Length <= 39 && key |> Seq.forall (fun c -> Char.IsLetter c || c = '0') then
                    errors
                else
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue
                            $"Expecting a portrait properties value, got %s{key}"
                            severity)
                        leafornode
                    <&&&> errors
            | ValueType.IRFamilyName ->
                let parts = key.Split('.')

                if (parts.Length <> 4) then
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue $"Expecting a family names value, got %s{key}" severity)
                        leafornode
                    <&&&> errors
                else
                    (LocalisationValidation.checkLocKeysLeafOrNodeN keys parts.[0] leafornode errors)
                    |> (LocalisationValidation.checkLocKeysLeafOrNodeN keys parts.[1] leafornode)
                    |> (LocalisationValidation.checkLocKeysLeafOrNodeN keys parts.[2] leafornode)
                    |> (LocalisationValidation.checkLocKeysLeafOrNodeN keys parts.[3] leafornode)
            | ValueType.STLNameFormat var ->
                match varMap.TryFind var with
                | Some vars ->
                    let refs = FieldValidatorsHelper.StlNameFormatRegex().Matches(key)

                    let refs =
                        refs
                        |> Seq.map _.Groups.[1]
                        |> Seq.cast<Text.RegularExpressions.Capture>
                        |> Seq.map _.Value

                    let res = refs |> Seq.exists (vars.Contains >> not)

                    if res then
                        inv
                            (ErrorCodes.CustomError $"Expecting a defined parts list of %s{var}" Severity.Error)
                            leafornode
                        <&&&> errors
                    else
                        OK
                | None -> errors


    let checkValidValueNE
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (enumsMap: FrozenDictionary<_, string * PrefixOptimisedStringSet>)
        (keys: (Lang * Collections.Set<string>) array)
        (vt: ValueType)
        (ids: StringTokens)
        =
        let key = getLowerKey ids

        (match vt with
         | ValueType.Bool -> key == "yes" || key == "no"
         | ValueType.Int(min, max) ->
             match TryParser.parseInt64WithDecimal key with
             | ValueSome i -> i <= max && i >= min
             | ValueNone ->
                 match enumsMap.TryFind "static_values" with
                 | Some(_, es) -> es.Contains(trimQuoteSpan key)
                 | None -> false
         | ValueType.Float(min, max) ->
             match TryParser.parseDecimal key with
             | ValueSome f -> f <= max && f >= min
             | ValueNone ->
                 match enumsMap.TryFind "static_values" with
                 | Some(_, es) -> es.Contains(trimQuoteSpan key)
                 | None -> false
         | ValueType.Enum e ->
             match enumsMap.TryFind e with
             | Some(_, es) -> es.Contains(trimQuoteSpan key)
             | None -> false
         | ValueType.Percent -> key.EndsWith('%')
         | ValueType.Date -> FieldValidatorsHelper.IsValidDate(key)
         | ValueType.DateTime -> FieldValidatorsHelper.IsValidDateTime(key)
         | ValueType.CK2DNA -> key.Length = CK2DnaLength && key |> Seq.forall (fun c -> Char.IsLetter c || c = '0')
         | ValueType.CK2DNAProperty -> key.Length <= 39 && key |> Seq.forall (fun c -> Char.IsLetter c || c = '0')
         | ValueType.IRFamilyName ->
             let parts = key.Split('.')

             (parts.Length = 4)
             && LocalisationValidation.checkLocKeysLeafOrNodeNE keys parts[0]
             && LocalisationValidation.checkLocKeysLeafOrNodeNE keys parts[1]
             && LocalisationValidation.checkLocKeysLeafOrNodeNE keys parts[2]
             && LocalisationValidation.checkLocKeysLeafOrNodeNE keys parts[3]
         | ValueType.STLNameFormat var ->
             match varMap.TryFind var with
             | Some vars ->
                 let refs = FieldValidatorsHelper.StlNameFormatRegex().Matches(key)

                 let res =
                     refs
                     |> Seq.map _.Groups[1]
                     |> Seq.cast<Text.RegularExpressions.Capture>
                     |> Seq.map _.Value
                     |> Seq.exists (vars.Contains >> not)

                 res |> not
             | None -> false)
        || firstCharEqualsAmp ids.lower

    let checkLocalisationField
        (processLocalisation:
            Lang * Collections.Map<string, CWTools.Localisation.Entry> -> Lang * Collections.Map<string, LocEntry>)
        (validateLocalisation: LocEntry -> ScopeContext -> ValidationResult)
        scopeContext
        (keys: (Lang * Collections.Set<string>) array)
        (defaultKeys: Collections.Set<string>)
        defaultLang
        (synced: bool)
        (isInline: bool)
        (ids: StringTokens)
        (leafornode: IKeyPos)
        errors
        =
        let key = trimQuote (getOriginalKey ids)
        let key =
            if key.StartsWith("text:", StringComparison.OrdinalIgnoreCase) then key.Substring(5)
            elif key.StartsWith("desc:", StringComparison.OrdinalIgnoreCase) then key.Substring(5)
            elif key.StartsWith("background:", StringComparison.OrdinalIgnoreCase) then key.Substring(11)
            elif key.StartsWith("icon:", StringComparison.OrdinalIgnoreCase) then key.Substring(5)
            else key

        match synced, isInline with
        | true, false ->
            // let defaultKeys = keys |> List.choose (fun (l, ks) -> if l = defaultLang then Some ks else None) |> List.tryHead |> Option.defaultValue Set.empty
            //let key = leaf.Value |> (function |QString s -> s |s -> s.ToString())
            LocalisationValidation.checkLocNameN leafornode defaultKeys defaultLang ids key errors
        | false, true -> LocalisationValidation.checkLocKeysInlineLeafOrNodeN keys ids key leafornode errors
        | false, false ->
            if key.Contains('[') then
                let entry =
                    { CWTools.Localisation.Entry.key = "inline"
                      CWTools.Localisation.Entry.value = None
                      CWTools.Localisation.Entry.desc = key
                      CWTools.Localisation.Entry.position = leafornode.Position
                      CWTools.Localisation.Entry.errorRange = None }

                let proc =
                    processLocalisation (defaultLang, Map.ofArray [| "inline", entry |])
                    |> snd
                    |> _.Values.First()

                validateLocalisation proc scopeContext
            else
                LocalisationValidation.checkLocKeysLeafOrNodeN keys key leafornode errors
        | _ -> errors

    let checkTypeField
        (typesMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        severity
        (typetype: TypeType)
        (ids: StringTokens)
        leafornode
        errors
        =
        let isComplex, fieldType =
            match typetype with
            | TypeType.Simple t -> false, t
            | Complex(_, t, _) -> true, t

        let key = getLowerKey ids

        match typesMap.TryFind fieldType with
        | Some values ->
            let value = trimQuote key
            let value =
                if value.StartsWith("text:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
                elif value.StartsWith("desc:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
                elif value.StartsWith("background:", StringComparison.OrdinalIgnoreCase) then value.Substring(11)
                elif value.StartsWith("icon:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
                else value

            if firstCharEqualsAmp ids.lower then
                errors
            else
                let newvalue =
                    match typetype with
                    | TypeType.Simple _ -> Some value
                    | Complex(p, _, s) ->
                        match
                            value.StartsWith(p, StringComparison.OrdinalIgnoreCase),
                            value.EndsWith(s, StringComparison.OrdinalIgnoreCase),
                            (value.Length - p.Length - s.Length)
                        with
                        | _, false, _ -> None
                        | false, _, _ -> None
                        | _, _, n when n <= 0 -> None
                        | true, true, n -> Some(value.Substring(p.Length, n))

                // eprintfn "ct %s %A %A" value newvalue typetype
                let found =
                    newvalue |> Option.map values.Contains |> Option.defaultValue false

                if found then
                    errors
                else
                    let suggestion =
                        match newvalue with
                        | Some v -> NameSuggestion.didYouMean v values.StringValues
                        | None -> ""

                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue
                            $"Expected value of type %s{fieldType}, got '%s{value}'%s{suggestion}"
                            severity)
                        leafornode
                    <&&&> errors

        //let values = values typeKeyMap values
        // if values.Contains value then errors else inv (ErrorCodes.ConfigRulesUnexpectedValue (sprintf "Expected value of type %s" fieldType) severity) leafornode <&&&> errors
        | None ->
            inv (ErrorCodes.CustomError $"Unknown type referenced %s{fieldType}" Severity.Error) leafornode
            <&&&> errors

    let private stripTypeFieldDecorators (value: string) =
        let value = trimQuote value

        if value.StartsWith("text:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
        elif value.StartsWith("desc:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
        elif value.StartsWith("background:", StringComparison.OrdinalIgnoreCase) then value.Substring(11)
        elif value.StartsWith("icon:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
        else value

    let private cleanTypeSuffixPattern (pattern: string) = pattern.Trim().Trim('"')

    let tryGetTypeSuffixPatternBaseValue (candidate: string) (pattern: string) =
        let pattern = cleanTypeSuffixPattern pattern

        if String.IsNullOrWhiteSpace pattern then
            None
        else
            let wildcardIndex = pattern.IndexOf('$')

            if wildcardIndex < 0 then
                if candidate.EndsWith(pattern, StringComparison.OrdinalIgnoreCase)
                   && candidate.Length > pattern.Length then
                    Some(candidate.Substring(0, candidate.Length - pattern.Length))
                else
                    None
            else
                let beforeWildcard = pattern.Substring(0, wildcardIndex)
                let afterWildcard = pattern.Substring(wildcardIndex + 1)

                if not (candidate.EndsWith(afterWildcard, StringComparison.OrdinalIgnoreCase)) then
                    None
                else
                    let body = candidate.Substring(0, candidate.Length - afterWildcard.Length)

                    let boundaryIndex =
                        if String.IsNullOrEmpty beforeWildcard then
                            body.Length
                        else
                            body.LastIndexOf(beforeWildcard, StringComparison.OrdinalIgnoreCase)

                    if boundaryIndex <= 0 then
                        None
                    else
                        let wildcardStart = boundaryIndex + beforeWildcard.Length

                        if wildcardStart >= body.Length then
                            None
                        else
                            Some(candidate.Substring(0, boundaryIndex))

    let typeSuffixPatternMatchesValue (value: string) (candidate: string) (pattern: string) =
        match tryGetTypeSuffixPatternBaseValue candidate pattern with
        | Some baseValue -> String.Equals(baseValue, value, StringComparison.OrdinalIgnoreCase)
        | None -> false

    let typeSuffixPatternBaseValues (values: seq<string>) (suffixPatterns: string list) =
        values
        |> Seq.collect (fun candidate ->
            suffixPatterns |> Seq.choose (tryGetTypeSuffixPatternBaseValue candidate))
        |> Seq.distinctBy (fun value -> value.ToLowerInvariant())

    let checkTypeFieldSuffixPatternNE
        (typesMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (typetype: TypeType)
        (ids: StringTokens)
        (suffixPatterns: string list)
        =
        match typetype, suffixPatterns with
        | TypeType.Simple fieldType, _ :: _ ->
            match typesMap.TryFindV fieldType with
            | ValueSome values ->
                if firstCharEqualsAmp ids.lower then
                    true
                else
                    let value = getLowerKey ids |> stripTypeFieldDecorators

                    values.StringValues
                    |> Seq.exists (fun candidate ->
                        suffixPatterns
                        |> List.exists (typeSuffixPatternMatchesValue value candidate))
            | ValueNone -> false
        | _ -> false

    let checkTypeFieldNE
        (typesMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (typetype: TypeType)
        (ids: StringTokens)
        =
        let isComplex, fieldType =
            match typetype with
            | TypeType.Simple t -> false, t
            | Complex(_, t, _) -> true, t

        let key = getLowerKey ids

        match typesMap.TryFindV fieldType with
        | ValueSome values ->
            let value = trimQuote key
            let value =
                if value.StartsWith("text:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
                elif value.StartsWith("desc:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
                elif value.StartsWith("background:", StringComparison.OrdinalIgnoreCase) then value.Substring(11)
                elif value.StartsWith("icon:", StringComparison.OrdinalIgnoreCase) then value.Substring(5)
                else value

            if firstCharEqualsAmp ids.lower then
                true
            else
                let value =
                    match typetype with
                    | TypeType.Simple _ -> ValueSome value
                    | Complex(p, _, s) ->
                        match
                            value.StartsWith(p, StringComparison.OrdinalIgnoreCase),
                            value.EndsWith(s, StringComparison.OrdinalIgnoreCase),
                            (value.Length - p.Length - s.Length)
                        with
                        | _, false, _ -> ValueNone
                        | false, _, _ -> ValueNone
                        | _, _, n when n <= 0 -> ValueNone
                        | true, true, n -> ValueSome(value.Substring(p.Length, n))

                value |> ValueOption.map values.Contains |> ValueOption.defaultValue false
        | ValueNone -> false

    let checkMacroTemplateMatch (value: string) (values: PrefixOptimisedStringSet) =
        values.StringValues |> Seq.exists (fun templateVar ->
            let idx = templateVar.IndexOf('$')
            if idx > 0 then
                value.StartsWith(templateVar.Substring(0, idx), StringComparison.OrdinalIgnoreCase)
            elif idx = 0 then
                let lastIdx = templateVar.LastIndexOf('$')
                if lastIdx < templateVar.Length - 1 && lastIdx >= 0 then
                    value.EndsWith(templateVar.Substring(lastIdx + 1), StringComparison.OrdinalIgnoreCase)
                else
                    true
            else
                false)

    let checkVariableGetField
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        severity
        (varName: string)
        (ids: StringTokens)
        leafornode
        errors
        =
        let key = getLowerKey ids

        match varMap.TryFind varName with
        | Some values ->
            let value = trimQuoteSpan key

            if firstCharEqualsAmp ids.lower then
                errors
            else if values.Contains value then
                errors
            else if value.Contains('@') && values.Contains(value.SplitFirst('@')) then
                errors
            else if (let result = values.LongestPrefixMatch(value) in result <> null) then
                errors
            else if checkMacroTemplateMatch (value.ToString()) values then
                errors
            else
                inv
                    (ErrorCodes.ConfigRulesUnexpectedValue
                        $"Expected defined value of %s{varName}, got %s{value.ToString()}"
                        (min Severity.Warning severity))
                    leafornode
                <&&&> errors
        | None ->
            inv
                (ErrorCodes.ConfigRulesUnexpectedValue
                    $"Expected defined value of %s{varName}, got %s{key}"
                    (min Severity.Warning severity))
                leafornode
            <&&&> errors

    let checkVariableGetFieldNE
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (varName: string)
        (ids: StringTokens)
        =
        let key = getLowerKey ids

        match varMap.TryFind varName with
        | Some values ->
            let value = trimQuoteSpan key

            if firstCharEqualsAmp ids.lower then
                true
            else
                values.Contains value
                || (value.Contains('@') && values.Contains(value.SplitFirst('@')))
                || (values.FindFirstByPrefix(value) <> null)
                || checkMacroTemplateMatch (value.ToString()) values
        | None -> false

    let private containsParameter (value: string) = value.IndexOf('$') >= 0

    let private isDynamicIdentifierChar c =
        Char.IsLetterOrDigit c
        || c = '_'
        || c = '.'
        || c = '-'

    let private isDynamicIdentifier (value: string) =
        value <> "" && value |> Seq.forall isDynamicIdentifierChar

    let private isExtendedIdentifierChar c =
        isDynamicIdentifierChar c
        || c = ':'
        || c = '/'
        || c = '\\'
        || c = '\''

    let private isExtendedIdentifier (value: string) =
        value <> "" && value |> Seq.forall isExtendedIdentifierChar

    let private dynamicValueName (value: string) =
        let atIndex = value.IndexOf('@')

        if atIndex >= 0 then
            value.Substring(0, atIndex)
        else
            value

    let private checkDynamicValueFieldNE
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (varName: string)
        (ids: StringTokens)
        =
        let key = trimQuote (getOriginalKey ids)

        if firstCharEqualsAmp ids.lower || containsParameter key then
            true
        else
            match varMap.TryFind varName with
            | Some values ->
                let value = key.AsSpan().Trim('\"')

                values.Contains value
                || (value.Contains('@') && values.Contains(value.SplitFirst('@')))
                || (values.FindFirstByPrefix(value) <> null)
                || checkMacroTemplateMatch (value.ToString()) values
            | None -> key |> dynamicValueName |> isDynamicIdentifier

    let private checkDynamicValueField
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        severity
        (varName: string)
        (ids: StringTokens)
        leafornode
        errors
        =
        if checkDynamicValueFieldNE varMap varName ids then
            errors
        else
            inv
                (ErrorCodes.ConfigRulesUnexpectedValue
                    $"Expected dynamic value of %s{varName}, got %s{trimQuote (getOriginalKey ids)}"
                    (min Severity.Warning severity))
                leafornode
            <&&&> errors

    let private splitByPipe (value: string) =
        value.Split([| '|' |], StringSplitOptions.None)

    let private checkScriptValueReferenceNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)

        if containsParameter key then
            true
        else
            let parts = splitByPipe key
            parts.Length >= 1 && isDynamicIdentifier parts.[0]

    let private checkDefineReferenceNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)

        if containsParameter key then
            true
        else
            match splitByPipe key with
            | [| ns; name |] -> isDynamicIdentifier ns && isDynamicIdentifier name
            | _ -> false

    let private checkArrayDefineReferenceNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)

        if containsParameter key then
            true
        else
            match splitByPipe key with
            | [| ns; name; index |] ->
                isDynamicIdentifier ns
                && isDynamicIdentifier name
                && (match Int32.TryParse index with | true, i -> i >= 0 | _ -> false)
            | _ -> false

    let private checkTagsFieldNE
        (varMap: FrozenDictionary<_, PrefixOptimisedStringSet>)
        (varName: string)
        condition
        (ids: StringTokens)
        =
        let key = trimQuote (getOriginalKey ids)

        if key = "" || containsParameter key then
            true
        else
            let values = varMap.TryFind varName

            let checkOne (raw: string) =
                let value = raw.Trim()

                let value =
                    if
                        condition
                        && value.StartsWith("not(", StringComparison.OrdinalIgnoreCase)
                        && value.EndsWith(")")
                    then
                        value.Substring(4, value.Length - 5).Trim()
                    else
                        value

                if value = "" then
                    false
                else
                    match values with
                    | Some known ->
                        let span = value.AsSpan()
                        known.Contains span
                        || (span.Contains('@') && known.Contains(span.SplitFirst('@')))
                        || (known.FindFirstByPrefix span <> null)
                    | None -> value |> dynamicValueName |> isDynamicIdentifier

            key.Split([| ',' |], StringSplitOptions.None)
            |> Array.forall checkOne

    let private checkDatabaseObjectNE
        (databaseObjectTypes: Map<string, DatabaseObjectTypeConfig>)
        (typesMap: FrozenDictionary<string, PrefixOptimisedStringSet>)
        (defaultLocalisation: Collections.Set<string>)
        (ids: StringTokens)
        =
        let key = trimQuote (getOriginalKey ids)

        if containsParameter key then
            true
        else
            let parts = key.Split([| ':' |], StringSplitOptions.None)

            let shapeOk =
                parts.Length >= 2 && parts |> Array.forall (fun p -> p.Trim() |> isDynamicIdentifier)

            let knownTypeValue (typeName: string) (value: string) =
                match typesMap.TryFind typeName with
                | Some values -> values.Contains(value)
                | None -> true

            let knownLocalisationValue (prefix: string) (value: string) =
                defaultLocalisation.Contains value
                || (not (String.IsNullOrWhiteSpace prefix) && defaultLocalisation.Contains(prefix + value))

            if not shapeOk then
                false
            elif Map.isEmpty databaseObjectTypes then
                true
            else
                let prefix = parts.[0].Trim()

                match databaseObjectTypes |> Map.tryFind prefix with
                | None -> false
                | Some config ->
                    let objectValue = parts.[1].Trim()

                    let objectOk =
                        match config.objectType, config.localisationPrefix with
                        | Some typeName, _ -> knownTypeValue typeName objectValue
                        | None, Some locPrefix -> knownLocalisationValue locPrefix objectValue
                        | None, None -> true

                    let swapOk =
                        if parts.Length < 3 then
                            true
                        else
                            match config.swapType with
                            | Some swapType -> knownTypeValue swapType (parts.[2].Trim())
                            | None -> false

                    objectOk && swapOk

    let private checkNameFormatNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)
        key <> "" || containsParameter key

    let private checkCommandNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)
        key <> "" || containsParameter key

    let private wildcardRegex kind (pattern: string) =
        match kind with
        | GlobPattern ->
            Regex.Escape(pattern).Replace(@"\*", ".*").Replace(@"\?", ".")
        | AntPattern ->
            Regex.Escape(pattern)
                .Replace(@"\*\*", ".*")
                .Replace(@"\*", @"[^/\\]*")
                .Replace(@"\?", @"[^/\\]")
        | RegexPattern -> pattern

    let private checkPatternFieldNE kind pattern ignoreCase (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)

        if containsParameter key then
            true
        else
            try
                let options =
                    RegexOptions.CultureInvariant
                    ||| if ignoreCase then
                            RegexOptions.IgnoreCase
                        else
                            RegexOptions.None

                Regex.IsMatch(
                    key,
                    $"^(?:%s{wildcardRegex kind pattern})$",
                    options
                )
            with _ ->
                false

    let private checkLooseExpressionNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)
        key <> "" || containsParameter key

    let private checkAbsoluteFilepathNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)

        containsParameter key
        || Regex.IsMatch(
            key,
            @"^(?:[A-Za-z]:[\\/]|[\\/]{2}[^\\/]+[\\/][^\\/]+|/).+",
            RegexOptions.CultureInvariant
        )

    let private checkFilenameFieldNE (files: FrozenSet<string>) (ids: StringTokens) (prefix: string option) =
        let key = (trimQuote (getOriginalKey ids)).Replace('\\', '/')

        if containsParameter key then
            true
        elif key = "" || key.Contains('/') then
            false
        else
            let normalisedPrefix =
                prefix
                |> Option.map (fun p -> p.Replace('\\', '/').Trim('/'))
                |> Option.filter (String.IsNullOrWhiteSpace >> not)

            files.Any(fun file ->
                let normalisedFile = file.Replace('\\', '/').Trim('/')

                let folderMatches =
                    match normalisedPrefix with
                    | Some p -> normalisedFile.StartsWith(p.TrimEnd('/') + "/", StringComparison.OrdinalIgnoreCase)
                    | None -> true

                folderMatches
                && String.Equals(
                    System.IO.Path.GetFileName normalisedFile,
                    key,
                    StringComparison.OrdinalIgnoreCase
                ))

    let private checkParameterNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)
        containsParameter key || isExtendedIdentifier key

    let private checkTechnologyWithLevelNE (ids: StringTokens) =
        let key = trimQuote (getOriginalKey ids)

        containsParameter key
        || Regex.IsMatch(
            key,
            "^[A-Za-z_][A-Za-z0-9_.:-]*(?:@[0-9]+)?$",
            RegexOptions.CultureInvariant
        )

    let private checkExtendedExpressionField name checkNE ids leafornode errors =
        if checkNE ids then
            errors
        else
            inv
                (ErrorCodes.ConfigRulesUnexpectedValue
                    $"Expected %s{name}, got %s{trimQuote (getOriginalKey ids)}"
                    Severity.Warning)
                leafornode
            <&&&> errors

    let checkFilepathField
        (files: FrozenSet<string>)
        (ids: StringTokens)
        (prefix: string option)
        (extension: string option)
        (fileExtensions: string list)
        leafornode
        severity
        errors
        =
        let normaliseExtension (extension: string) =
            extension.Trim().TrimStart('.').ToLowerInvariant()

        let allowedExtensions =
            fileExtensions
            |> List.map normaliseExtension
            |> List.filter (String.IsNullOrWhiteSpace >> not)
            |> List.distinct

        let checkWith extension =
            FieldValidatorsHelper.CheckFilePathField(getOriginalKey ids, files, prefix, extension, false) |> fst

        let isValid =
            match allowedExtensions with
            | [] -> checkWith extension
            | allowed ->
                match extension with
                | Some ext when allowed |> List.contains (normaliseExtension ext) -> checkWith extension
                | Some _ -> false
                | None ->
                    let key =
                        (trimQuote (getOriginalKey ids)).Replace('\\', '/')

                    let keyExtension =
                        System.IO.Path.GetExtension(key) |> normaliseExtension

                    if keyExtension <> "" then
                        (allowed |> List.contains keyExtension) && checkWith None
                    else
                        allowed |> List.exists (fun ext -> checkWith (Some("." + ext)))

        if isValid then
            errors
        elif allowedExtensions.IsEmpty then
            let _, file =
                FieldValidatorsHelper.CheckFilePathField(getOriginalKey ids, files, prefix, extension, true)

            inv (ErrorCodes.MissingFile file) leafornode <&&&> errors
        else
            let allowedText =
                allowedExtensions
                |> List.map (fun ext -> "." + ext)
                |> String.concat ", "

            inv
                (ErrorCodes.CustomError
                    $"Expected file path with extension %s{allowedText}, got %s{trimQuote (getOriginalKey ids)}"
                    severity)
                leafornode
            <&&&> errors

    let checkFilepathFieldNE
        (files: FrozenSet<string>)
        (ids: StringTokens)
        (prefix: string option)
        (extension: string option)
        (fileExtensions: string list)
        =
        let normaliseExtension (extension: string) =
            extension.Trim().TrimStart('.').ToLowerInvariant()

        let allowedExtensions =
            fileExtensions
            |> List.map normaliseExtension
            |> List.filter (String.IsNullOrWhiteSpace >> not)
            |> List.distinct

        let checkWith extension =
            FieldValidatorsHelper.CheckFilePathField(getOriginalKey ids, files, prefix, extension, false) |> fst

        match allowedExtensions with
        | [] -> checkWith extension
        | allowed ->
            match extension with
            | Some ext when allowed |> List.contains (normaliseExtension ext) -> checkWith extension
            | Some _ -> false
            | None ->
                let key =
                    (trimQuote (getOriginalKey ids)).Replace('\\', '/')

                let keyExtension =
                    System.IO.Path.GetExtension(key) |> normaliseExtension

                if keyExtension <> "" then
                    (allowed |> List.contains keyExtension) && checkWith None
                else
                    allowed |> List.exists (fun ext -> checkWith (Some("." + ext)))

    let private fileExistsIgnoringCase (files: FrozenSet<string>) (file: string) =
        files.Any(fun existing -> existing.Equals(file, System.StringComparison.OrdinalIgnoreCase))

    let checkIconField (files: FrozenSet<string>) (folder: string) (ids: StringTokens) leafornode errors =
        let lookup = files.GetAlternateLookup<ReadOnlySpan<char>>()

        use sb = ZString.CreateStringBuilder()
        let key = trimQuoteSpan (getOriginalKey ids)
        sb.Append folder
        sb.Append '/'
        sb.Append key
        sb.Append ".dds"

        if lookup.Contains(sb.AsSpan()) || fileExistsIgnoringCase files (sb.ToString()) then
            errors
        else
            inv (ErrorCodes.MissingFile(sb.ToString())) leafornode <&&&> errors

    let checkIconFieldNE (files: FrozenSet<string>) (folder: string) (ids: StringTokens) =
        let lookup = files.GetAlternateLookup<ReadOnlySpan<char>>()

        use sb = ZString.CreateStringBuilder()
        let key = trimQuoteSpan (getOriginalKey ids)
        sb.Append folder
        sb.Append '/'
        sb.Append key
        sb.Append ".dds"

        lookup.Contains(sb.AsSpan()) || fileExistsIgnoringCase files (sb.ToString())

    let private isScopeNamed name (scope: Scope) =
        String.Equals(scope.ToString(), name, StringComparison.OrdinalIgnoreCase)

    /// Stellaris Carrier is a synthetic Planet-or-Ship union rather than a
    /// concrete scope. Target fields must accept the union when either host is
    /// allowed, including while validating expanded inline scripts.
    let private carrierScopeMatches (scopes: Scope list) (currentScope: Scope) =
        let isCarrierHost scope = isScopeNamed "Planet" scope || isScopeNamed "Ship" scope

        isScopeNamed "Carrier" currentScope && List.exists isCarrierHost scopes

    let private checkAnyScopesMatch anyScope (scopes: Scope list) (currentScope: Scope) =
        (currentScope = anyScope)
        || (List.exists (fun s -> currentScope.IsOfScope(s) || s = anyScope) scopes)
        || carrierScopeMatches scopes currentScope

    let checkScopeField
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        varSet
        (changeScope: ChangeScope)
        anyScope
        (ctx: RuleContext)
        s
        (ids: StringTokens)
        leafornode
        errors
        =
        let key = getOriginalKey ids
        let key = key.Trim('"')
        let scope = ctx.scopes

        match changeScope.Invoke(false, true, linkMap, valueTriggerMap, wildcardLinks, varSet, key, scope) with
        | ScopeResult.NewScope({ Scopes = current :: _ }, _, _) ->
            if checkAnyScopesMatch anyScope s current then
                errors
            else
                inv (ErrorCodes.ConfigRulesTargetWrongScope (current.ToString()) (s.ToString()) key) leafornode
                <&&&> errors
        | NotFound ->
            inv (ErrorCodes.ConfigRulesInvalidTarget (s.ToString()) key) leafornode
            <&&&> errors
        | ScopeResult.WrongScope(command, prevscope, expected, _) ->
            inv (ErrorCodes.ConfigRulesErrorInTarget command (prevscope.ToString()) $"{expected}") leafornode
            <&&&> errors
        | VarFound -> errors
        | VarNotFound s -> inv (ErrorCodes.ConfigRulesUnsetVariable s) leafornode <&&&> errors
        | ValueFound _ ->
            inv (ErrorCodes.CustomError "This is a value, but should be a scope" Severity.Error) leafornode
            <&&&> errors
        | _ -> errors

    let checkScopeFieldNE
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        varSet
        (changeScope: ChangeScope)
        anyScope
        (ctx: RuleContext)
        s
        (ids: StringTokens)
        =
        // log "scope %s %A"key ctx
        let key = getOriginalKey(ids).AsSpan()
        let key = key.Trim('"')

        match changeScope.Invoke(true, true, linkMap, valueTriggerMap, wildcardLinks, varSet, key, ctx.scopes) with
        | ScopeResult.NewScope({ Scopes = current :: _ }, _, _) -> checkAnyScopesMatch anyScope s current
        | NotFound -> false
        | ScopeResult.WrongScope _ -> true
        | VarNotFound _ -> false
        | ValueFound _ -> false
        | _ -> true

    let checkVariableField
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        varSet
        (changeScope: ChangeScope)
        (ctx: RuleContext)
        isInt
        is32Bit
        min
        max
        (ids: StringTokens)
        leafornode
        errors
        =
        let scope = ctx.scopes
        let key = getOriginalKey(ids).AsSpan()
        let metadata = getStringMetadata ids.lower

        if metadata.startsWithAmp || key.IndexOf('$') >= 0 then
            errors
        else
            let key =
                match metadata.containsQuestionMark, metadata.containsHat with
                | true, _ -> key.SplitFirst('?')
                | false, true -> key.SplitFirst('^')
                | _ -> key

            match
                TryParser.parseDecimalSpan key,
                TryParser.parseInt64Span key,
                changeScope.Invoke(false, true, linkMap, valueTriggerMap, wildcardLinks, varSet, key, scope)
            with
            | _, ValueSome i, _ when isInt && min <= decimal i && max >= decimal i -> errors
            | ValueSome f, _, _ when (not isInt) && min <= f && max >= f && ((not is32Bit) || (f = Math.Round(f, 3))) ->
                errors
            | ValueSome f, _, _ when min <= f && max >= f ->
                inv ErrorCodes.ConfigRulesVariableTooSmall leafornode <&&&> errors
            | ValueSome f, _, _ when isInt -> inv ErrorCodes.ConfigRulesVariableIntOnly leafornode <&&&> errors
            | _, _, VarFound -> errors
            | _, _, VarNotFound s -> inv (ErrorCodes.ConfigRulesUnsetVariable s) leafornode <&&&> errors
            | _, _, ScopeResult.WrongScope(command, prevscope, expected, refHint) ->
                Invalid(
                    Guid.NewGuid(),
                    [ inv
                          (ErrorCodes.ConfigRulesErrorInTarget command (prevscope.ToString()) $"%A{expected}")
                          leafornode ]
                )
            | _, _, NotFound ->
                if checkMacroTemplateMatch (key.ToString()) varSet then
                    errors
                else
                    inv ErrorCodes.ConfigRulesExpectedVariableValue leafornode <&&&> errors
            | _ ->
                inv (ErrorCodes.CustomError "Expecting a variable, but got a scope" Severity.Information) leafornode
                <&&&> errors

    let checkVariableFieldNE
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        (varSet: PrefixOptimisedStringSet)
        (changeScope: ChangeScope)
        (ctx: RuleContext)
        isInt
        is32Bit
        min
        max
        (ids: StringTokens)
        =
        let scope = ctx.scopes
        let metadata = getStringMetadata ids.lower
        let key = getOriginalKey(ids).AsSpan()

        if metadata.startsWithAmp || key.IndexOf('$') >= 0 then
            true
        else

            let key =
                match metadata.containsQuestionMark, metadata.containsHat with
                | true, _ -> key.SplitFirst('?')
                | false, true -> key.SplitFirst('^')
                | _ -> key

            match
                TryParser.parseDecimalSpan key,
                TryParser.parseInt64Span key,
                changeScope.Invoke(false, true, linkMap, valueTriggerMap, wildcardLinks, varSet, key, scope)
            with
            | _, ValueSome i, _ -> isInt && min <= decimal i && max >= decimal i
            | ValueSome f, _, _ -> min <= f && max >= f && ((not is32Bit) || (f = Math.Round(f, 3)))
            | _, _, VarFound -> true
            | _, _, VarNotFound _ -> false
            | _ -> false

    let checkValueScopeField
        (enumsMap: FrozenDictionary<_, string * PrefixOptimisedStringSet>)
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        varSet
        (changeScope: ChangeScope)
        (ctx: RuleContext)
        isInt
        min
        max
        (ids: StringTokens)
        leafornode
        errors
        =
        let scope = ctx.scopes
        // let res = changeScope false true linkMap valueTriggerMap varSet key scope
        let metadata = getStringMetadata ids.lower
        let key = getOriginalKey ids

        let key =
            match metadata.containsPipe with
            | true -> key.AsSpan().SplitFirst('|')
            | _ -> key.AsSpan()

        let scopeResult =
            changeScope.Invoke(false, true, linkMap, valueTriggerMap, wildcardLinks, varSet, key, scope)

        let scopeResult =
            match scopeResult with
            | ScopeResult.ValueFound _
            | ScopeResult.VarFound
            | ScopeResult.VarNotFound _
            | ScopeResult.WrongScope _ -> scopeResult
            | _ ->
                tryResolveScopedTriggerValue linkMap valueTriggerMap wildcardLinks varSet changeScope scope key
                |> Option.defaultValue scopeResult

        match firstCharEqualsAmp ids.lower || key.IndexOf('$') >= 0, TryParser.parseDecimalSpan key, TryParser.parseInt64Span key, scopeResult with
        | true, _, _, _ -> errors
        | _, _, ValueSome i, _ when isInt && min <= decimal i && max >= decimal i -> errors
        | _, ValueSome f, _, _ when min <= f && max >= f -> errors
        | _, _, _, VarFound -> errors
        | _, _, _, VarNotFound s -> inv (ErrorCodes.ConfigRulesUnsetVariable s) leafornode <&&&> errors
        | _, _, _, ValueFound _ -> errors
        | _, _, _, ScopeResult.WrongScope(command, prevscope, expected, refHint) ->
            inv (ErrorCodes.ConfigRulesErrorInTarget command (prevscope.ToString()) $"%A{expected}") leafornode
            <&&&> errors
        | _, _, _, NotFound ->
            let keyText = key.ToString()

            if keyText.StartsWith("value:", StringComparison.OrdinalIgnoreCase) then
                let valueName = keyText.Substring("value:".Length)

                inv
                    (ErrorCodes.CustomError $"Script value %s{valueName} is not defined" Severity.Error)
                    leafornode
                <&&&> errors
            elif checkMacroTemplateMatch keyText varSet then
                errors
            else
                match enumsMap.TryFind "static_values" with
                | Some(_, es) ->
                    if es.Contains(key.Trim('\"')) then
                        errors
                    else
                        inv ErrorCodes.ConfigRulesExpectedVariableValue leafornode <&&&> errors
                | None -> inv ErrorCodes.ConfigRulesExpectedVariableValue leafornode <&&&> errors
        | _ ->
            inv (ErrorCodes.CustomError "Expecting a variable, but got a scope" Severity.Information) leafornode
            <&&&> errors

    let checkValueScopeFieldNE
        (enumsMap: FrozenDictionary<_, string * PrefixOptimisedStringSet>)
        (linkMap: EffectMap)
        (valueTriggerMap: EffectMap)
        (wildcardLinks: ScopedEffect list)
        varSet
        (changeScope: ChangeScope)
        (ctx: RuleContext)
        isInt
        min
        max
        (ids: StringTokens)
        =
        let scope = ctx.scopes
        let key = getOriginalKey ids

        let scopeResult =
            changeScope.Invoke(false, true, linkMap, valueTriggerMap, wildcardLinks, varSet, key, scope)

        let scopeResult =
            match scopeResult with
            | ScopeResult.ValueFound _
            | ScopeResult.VarFound
            | ScopeResult.VarNotFound _
            | ScopeResult.WrongScope _ -> scopeResult
            | _ ->
                tryResolveScopedTriggerValue linkMap valueTriggerMap wildcardLinks varSet changeScope scope (key.AsSpan())
                |> Option.defaultValue scopeResult

        match firstCharEqualsAmp ids.lower || key.IndexOf('$') >= 0, TryParser.parseDecimal key, TryParser.parseInt64 key, scopeResult with
        | true, _, _, _ -> true
        | _, _, ValueSome i, _ -> isInt && min <= decimal i && max >= decimal i
        | _, ValueSome f, _, _ -> min <= f && max >= f
        | _, _, _, VarFound -> true
        | _, _, _, VarNotFound s -> false
        | _, _, _, ValueFound _ -> true
        | _, _, _, NotFound ->
            match enumsMap.TryFind "static_values" with
            | Some(_, es) -> es.Contains(trimQuoteSpan key)
            | None -> false

        | _ -> false

    let checkAliasValueKeysField
        (aliasKeyList: Collections.Map<string, HashSet<StringToken>>)
        aliasKey
        (ids: StringTokens)
        severity
        leafornode
        errors
        =
        let key = getOriginalKey ids

        match aliasKeyList |> Map.tryFind aliasKey with
        | Some values ->
            if values.Contains ids.lower then
                errors
            else
                inv (ErrorCodes.ConfigRulesUnexpectedAliasKeyValue aliasKey key severity) leafornode
                <&&&> errors
        | None ->
            inv (ErrorCodes.ConfigRulesUnexpectedAliasKeyValue aliasKey key severity) leafornode
            <&&&> errors

    let checkAliasValueKeysFieldNE
        (aliasKeyList: Collections.Map<string, HashSet<StringToken>>)
        aliasKey
        (ids: StringTokens)
        =
        match aliasKeyList |> Map.tryFind aliasKey with
        | Some values -> values.Contains ids.lower
        | None -> true

    let rec checkField
        (p: CheckFieldParams)
        (severity: Severity)
        (ctx: RuleContext)
        (field: NewField)
        (keyIDs: StringTokens)
        (leafornode: IKeyPos)
        errors
        =
        let keyIDs =
            let metadata = (stringManager.GetMetadataForID keyIDs.lower)
            if metadata.startsWithSquareBracket then
                let keyStr = stringManager.GetStringForIDs keyIDs
                if keyStr.StartsWith("[[") && keyStr.Contains("]") then
                    let prefixEnd = keyStr.IndexOf(']')
                    if prefixEnd >= 0 && prefixEnd + 1 < keyStr.Length then
                        stringManager.InternIdentifierToken (keyStr.Substring(prefixEnd + 1))
                    else
                        keyIDs
                else
                    keyIDs
            else
                keyIDs

        let metadataForId = (stringManager.GetMetadataForID keyIDs.lower)

        if metadataForId.containsDoubleDollar || metadataForId.startsWithSquareBracket then
            errors
        else
            match field with
            | ValueField vt -> checkValidValue p.varMap p.enumsMap p.localisation severity vt keyIDs leafornode errors
            | TypeField t -> checkTypeField p.typesMap severity t keyIDs leafornode errors
            | ScopeField s ->
                checkScopeField
                    p.linkMap
                    p.valueTriggerMap
                    p.wildcardLinks
                    p.varSet
                    p.changeScope
                    p.anyScope
                    ctx
                    s
                    keyIDs
                    leafornode
                    errors
            | LocalisationField(synced, isInline) ->
                checkLocalisationField
                    p.processLocalisation
                    p.validateLocalisation
                    ctx.scopes
                    p.localisation
                    p.defaultLocalisation
                    p.defaultLang
                    synced
                    isInline
                    keyIDs
                    leafornode
                    errors
            | FilepathField(prefix, extension) ->
                checkFilepathField p.files keyIDs prefix extension [] leafornode severity errors
            | FilenameField prefix ->
                if checkFilenameFieldNE p.files keyIDs prefix then
                    errors
                else
                    inv
                        (ErrorCodes.CustomError
                            $"Expected filename, got %s{trimQuote (getOriginalKey keyIDs)}"
                            severity)
                        leafornode
                    <&&&> errors
            | AbsoluteFilepathField ->
                checkExtendedExpressionField "absolute file path" checkAbsoluteFilepathNE keyIDs leafornode errors
            | IconField folder -> checkIconField p.files folder keyIDs leafornode errors
            | VariableSetField v -> errors
            | VariableGetField v -> checkVariableGetField p.varMap severity v keyIDs leafornode errors
            | DynamicValueField v -> checkDynamicValueField p.varMap severity v keyIDs leafornode errors
            | VariableField(isInt, is32Bit, (min, max)) ->
                checkVariableField
                    p.linkMap
                    p.valueTriggerMap
                    p.wildcardLinks
                    p.varSet
                    p.changeScope
                    ctx
                    isInt
                    is32Bit
                    min
                    max
                    keyIDs
                    leafornode
                    errors
            | ValueScopeField(isInt, (min, max)) ->
                checkValueScopeField
                    p.enumsMap
                    p.linkMap
                    p.valueTriggerMap
                    p.wildcardLinks
                    p.varSet
                    p.changeScope
                    ctx
                    isInt
                    min
                    max
                    keyIDs
                    leafornode
                    errors
            | CommandField -> checkExtendedExpressionField "command expression" checkCommandNE keyIDs leafornode errors
            | ScriptValueReferenceField ->
                checkExtendedExpressionField
                    "script value reference"
                    checkScriptValueReferenceNE
                    keyIDs
                    leafornode
                    errors
            | DefineReferenceField ->
                checkExtendedExpressionField "define reference" checkDefineReferenceNE keyIDs leafornode errors
            | ArrayDefineReferenceField ->
                checkExtendedExpressionField
                    "array define reference"
                    checkArrayDefineReferenceNE
                    keyIDs
                    leafornode
                    errors
            | TagsField(name, condition) ->
                if checkTagsFieldNE p.varMap name condition keyIDs then
                    errors
                else
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue
                            $"Expected tags expression of %s{name}, got %s{trimQuote (getOriginalKey keyIDs)}"
                            Severity.Warning)
                        leafornode
                    <&&&> errors
            | DatabaseObjectField ->
                checkExtendedExpressionField
                    "database object expression"
                    (checkDatabaseObjectNE p.databaseObjectTypes p.typesMap p.defaultLocalisation)
                    keyIDs
                    leafornode
                    errors
            | NameFormatField _ -> checkExtendedExpressionField "name format expression" checkNameFormatNE keyIDs leafornode errors
            | PatternField(kind, pattern, ignoreCase) ->
                if checkPatternFieldNE kind pattern ignoreCase keyIDs then
                    errors
                else
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue
                            $"Expected value matching %A{kind} pattern %s{pattern}, got %s{trimQuote (getOriginalKey keyIDs)}"
                            severity)
                        leafornode
                    <&&&> errors
            | ShaderEffectField ->
                checkExtendedExpressionField "shader effect expression" checkLooseExpressionNE keyIDs leafornode errors
            | MeshLocatorField ->
                checkExtendedExpressionField "mesh locator expression" checkLooseExpressionNE keyIDs leafornode errors
            | TechnologyWithLevelField ->
                checkExtendedExpressionField
                    "technology-with-level expression"
                    checkTechnologyWithLevelNE
                    keyIDs
                    leafornode
                    errors
            | ParameterField -> checkExtendedExpressionField "parameter expression" checkParameterNE keyIDs leafornode errors
            | ParameterValueField ->
                checkExtendedExpressionField "parameter value expression" checkLooseExpressionNE keyIDs leafornode errors
            | LocalisationParameterField ->
                checkExtendedExpressionField
                    "localisation parameter expression"
                    checkParameterNE
                    keyIDs
                    leafornode
                    errors
            | PrefixedField inner ->
                checkField p severity ctx inner (stripPrefixedValueIds keyIDs) leafornode errors
            | ScalarField _ -> errors
            | SpecificField(SpecificValue v) ->
                if keyIDs.lower = v.lower then
                    errors
                else
                    inv
                        (ErrorCodes.ConfigRulesUnexpectedValue
                            $"Expecting value %s{StringResource.stringManager.GetStringForID(v.normal)}"
                            severity)
                        leafornode
                    <&&&> errors
            | AliasField _
            | AliasParamsField _ -> errors
            | MarkerField _
            | SingleAliasField _
            | SubtypeField _
            | TypeMarkerField _
            | IgnoreMarkerField
            | ValueScopeMarkerField _ ->
                inv (ErrorCodes.CustomError $"Unexpected rule type {field}" Severity.Error) leafornode
                <&&&> errors
            | AliasValueKeysField aliasKey ->
                checkAliasValueKeysField p.aliasKeys aliasKey keyIDs severity leafornode errors
            | IgnoreField field -> checkField p severity ctx field keyIDs leafornode errors
            // Should never happen
            | SingleAliasClauseField _ -> errors
            | JominiGuiField -> errors

    let rec checkFieldNE
        (p: CheckFieldParams)
        (severity: Severity)
        (ctx: RuleContext)
        (field: NewField)
        (keyIDs: StringTokens)
        =
        let keyIDs =
            let metadata = (stringManager.GetMetadataForID keyIDs.lower)
            if metadata.startsWithSquareBracket then
                let keyStr = stringManager.GetStringForIDs keyIDs
                if keyStr.StartsWith("[[") && keyStr.Contains("]") then
                    let prefixEnd = keyStr.IndexOf(']')
                    if prefixEnd >= 0 && prefixEnd + 1 < keyStr.Length then
                        stringManager.InternIdentifierToken (keyStr.Substring(prefixEnd + 1))
                    else
                        keyIDs
                else
                    keyIDs
            else
                keyIDs

        let metadataForId = (stringManager.GetMetadataForID keyIDs.lower)

        if metadataForId.containsDoubleDollar || metadataForId.startsWithSquareBracket then
            true
        else
            match field with
            | ValueField vt -> checkValidValueNE p.varMap p.enumsMap p.localisation vt keyIDs
            | TypeField t -> checkTypeFieldNE p.typesMap t keyIDs
            | ScopeField s ->
                checkScopeFieldNE
                    p.linkMap
                    p.valueTriggerMap
                    p.wildcardLinks
                    p.varSet
                    p.changeScope
                    p.anyScope
                    ctx
                    s
                    keyIDs
            | LocalisationField _ -> true
            | FilepathField(prefix, extension) -> checkFilepathFieldNE p.files keyIDs prefix extension []
            | FilenameField prefix -> checkFilenameFieldNE p.files keyIDs prefix
            | AbsoluteFilepathField -> checkAbsoluteFilepathNE keyIDs
            | IconField folder -> checkIconFieldNE p.files folder keyIDs
            | VariableSetField _ -> true
            | VariableGetField v -> checkVariableGetFieldNE p.varMap v keyIDs
            | DynamicValueField v -> checkDynamicValueFieldNE p.varMap v keyIDs
            | VariableField(isInt, is32Bit, (min, max)) ->
                checkVariableFieldNE
                    p.linkMap
                    p.valueTriggerMap
                    p.wildcardLinks
                    p.varSet
                    p.changeScope
                    ctx
                    isInt
                    is32Bit
                    min
                    max
                    keyIDs
            | ValueScopeField(isInt, (min, max)) ->
                checkValueScopeFieldNE
                    p.enumsMap
                    p.linkMap
                    p.valueTriggerMap
                    p.wildcardLinks
                    p.varSet
                    p.changeScope
                    ctx
                    isInt
                    min
                    max
                    keyIDs
            | CommandField -> checkCommandNE keyIDs
            | ScriptValueReferenceField -> checkScriptValueReferenceNE keyIDs
            | DefineReferenceField -> checkDefineReferenceNE keyIDs
            | ArrayDefineReferenceField -> checkArrayDefineReferenceNE keyIDs
            | TagsField(name, condition) -> checkTagsFieldNE p.varMap name condition keyIDs
            | DatabaseObjectField -> checkDatabaseObjectNE p.databaseObjectTypes p.typesMap p.defaultLocalisation keyIDs
            | NameFormatField _ -> checkNameFormatNE keyIDs
            | PatternField(kind, pattern, ignoreCase) -> checkPatternFieldNE kind pattern ignoreCase keyIDs
            | ShaderEffectField -> checkLooseExpressionNE keyIDs
            | MeshLocatorField -> checkLooseExpressionNE keyIDs
            | TechnologyWithLevelField -> checkTechnologyWithLevelNE keyIDs
            | ParameterField -> checkParameterNE keyIDs
            | ParameterValueField -> checkLooseExpressionNE keyIDs
            | LocalisationParameterField -> checkParameterNE keyIDs
            | PrefixedField inner -> checkFieldNE p severity ctx inner (stripPrefixedValueIds keyIDs)
            | TypeMarkerField(dummy, _) -> dummy = keyIDs.lower
            | ScalarField _ -> true
            | SpecificField(SpecificValue v) -> v.lower = keyIDs.lower
            | AliasField _
            | AliasParamsField _
            | MarkerField _
            | SingleAliasField _
            | SubtypeField _
            | TypeMarkerField _
            | IgnoreMarkerField
            | ValueScopeMarkerField _ -> false
            | AliasValueKeysField aliasKey -> checkAliasValueKeysFieldNE p.aliasKeys aliasKey keyIDs
            | IgnoreField field -> checkFieldNE p severity ctx field keyIDs
            // Should never happen
            | SingleAliasClauseField _ -> failwith "todo"
            | JominiGuiField -> false

    let checkLeftField (p: CheckFieldParams) (severity: Severity) (ctx: RuleContext) (field: NewField) keyIDs =
        checkFieldNE p severity ctx field keyIDs

    let checkFieldByKey (p: CheckFieldParams) (severity: Severity) (ctx: RuleContext) (field: NewField) keyIDs =
        checkLeftField p severity ctx field keyIDs

    let inline validateTypeLocalisation
        (typedefs: TypeDefinition list)
        (invertedTypeMap: IDictionary<string, ResizeArray<string>>)
        localisation
        (typeKey: string)
        (key: string)
        leafornode
        =
        let typeNames = typeKey.Split('.')
        let typename = typeNames[0]

        let actualSubtypes =
            match invertedTypeMap.TryGetValue key with
            | true, keytypes ->
                keytypes
                |> Seq.filter (fun kt -> kt.StartsWith(typename + ".", StringComparison.OrdinalIgnoreCase))
                |> Seq.map (fun kt -> kt.Split('.').[1])
                |> Seq.toList
            | false, _ -> []

        match typedefs |> List.tryFind (fun t -> t.name == typename) with
        | None -> OK
        | Some typedef ->
            let inner =
                (fun (l: TypeLocalisation) ->
                    let lockey = l.prefix + key + l.suffix

                    if l.optional || l.explicitField.IsSome then
                        OK
                    else
                        CWTools.Validation.Stellaris.STLLocalisationValidation.checkLocKeysLeafOrNode
                            localisation
                            lockey
                            leafornode)

            let subtype =
                let subtypes =
                    (if typeNames.Length > 1 then
                         typeNames.[1] :: actualSubtypes
                     else
                         actualSubtypes)
                    |> List.distinct

                let inner2 (nextSt: string) =
                    match typedef.subtypes |> List.tryFind (fun st -> st.name == nextSt) with
                    | None -> OK
                    | Some st -> st.localisation <&!&> inner

                subtypes <&!&> inner2

            typedef.localisation <&!&> inner <&&> subtype

    let typekeyfilter (td: TypeDefinition) (n: string) (keyPrefix: string option) =
        match td.typeKeyFilter with
        | Some(values, negate) -> (values |> List.exists ((==) n)) <> negate
        | None -> true
        && match td.startsWith with
           | Some prefix -> n.StartsWith(prefix, StringComparison.OrdinalIgnoreCase)
           | None -> true
        && match td.typeKeyRegex with
           | Some pattern ->
               try
                   Regex.IsMatch(
                       n,
                       pattern,
                       RegexOptions.IgnoreCase ||| RegexOptions.CultureInvariant
                   )
               with _ ->
                   false
           | None -> true
        && match td.keyPrefix, keyPrefix with
           | Some prefix, Some keyPrefix -> prefix == keyPrefix
           | None, None -> true
           | _ -> false
