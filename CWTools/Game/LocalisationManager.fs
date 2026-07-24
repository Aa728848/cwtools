namespace CWTools.Games

open System
open System.Collections.Generic
open System.IO
open CWTools.Common
open CWTools.Localisation
open CWTools.Process.Localisation
open CWTools.Utilities.Utils
open FSharp.Collections.ParallelSeq

[<Sealed>]
type LocalisationManager<'T when 'T :> ComputedData>
    (
        resources: IResourceAPI<'T>,
        localisationService: _ -> ILocalisationAPICreator,
        langs: Lang array,
        lookup: Lookup,
        processLocalisation,
        localisationExtension: string
    ) as this =
    let mutable localisationAPIMap: Map<string * Lang, struct (bool * ILocalisationAPI)> =
        Map.empty

    // Most localisation keys have a single provider. Store counts only for the
    // sparse duplicate case; the tagged set itself represents count = 1.
    let duplicateLocalisationKeyCounts = Dictionary<Lang, Dictionary<string, int>>()
    let mutable localisationKeySets: Map<Lang, Set<string>> = Map.empty
    let taggedKeySets = Dictionary<Lang, LocKeySet>()
    let pathComparer = if OperatingSystem.IsWindows() then StringComparer.OrdinalIgnoreCase else StringComparer.Ordinal
    let processedReferencesBySource = Dictionary<struct (Lang * string), string array>()
    let processedSourcesByReference = Dictionary<struct (Lang * string), HashSet<string>>()
    let mutable pendingDelta: LocalisationDelta option = None

    let validatableLocalisation () =
        this.GetLocalisationAPIs()
        |> List.choose (fun struct (validate, api) -> if validate then Some api else None)

    let parseLocFile (locFile: FileWithContentResource) =
        if
            locFile.overwrite <> Overwrite.Overwritten
            && Path
                .GetExtension(locFile.filepath.AsSpan())
                .Equals(localisationExtension, StringComparison.OrdinalIgnoreCase)
        then
            let locService = [ locFile.filepath, locFile.filetext ] |> localisationService

            Some(
                langs
                |> Array.map (fun lang -> (locFile.filepath, lang), struct (locFile.validate, locService.Api(lang)))
            )
        else
            None

    let duplicateKeyCountMap lang =
        match duplicateLocalisationKeyCounts.TryGetValue lang with
        | true, counts -> counts
        | false, _ ->
            let counts = Dictionary<string, int>(StringComparer.Ordinal)
            duplicateLocalisationKeyCounts.Add(lang, counts)
            counts

    let addKeys lang (keys: string array) =
        let tagged =
            match taggedKeySets.TryGetValue lang with
            | true, existing -> existing
            | false, _ ->
                let created = LocKeySet(StringComparer.Ordinal)
                taggedKeySets.Add(lang, created)
                created
        for key in keys do
            if tagged.Add key then
                let current = localisationKeySets |> Map.tryFind lang |> Option.defaultValue Set.empty
                localisationKeySets <- Map.add lang (Set.add key current) localisationKeySets
            else
                let duplicateCounts = duplicateKeyCountMap lang
                match duplicateCounts.TryGetValue key with
                | true, count -> duplicateCounts.[key] <- count + 1
                | false, _ -> duplicateCounts.Add(key, 2)

    let removeKeys lang (keys: string array) =
        for key in keys do
            let mutable removeLastProvider = true
            match duplicateLocalisationKeyCounts.TryGetValue lang with
            | true, duplicateCounts ->
                match duplicateCounts.TryGetValue key with
                | true, count when count > 2 ->
                    duplicateCounts.[key] <- count - 1
                    removeLastProvider <- false
                | true, _ ->
                    duplicateCounts.Remove key |> ignore
                    if duplicateCounts.Count = 0 then duplicateLocalisationKeyCounts.Remove lang |> ignore
                    removeLastProvider <- false
                | false, _ -> ()
            | false, _ -> ()

            if removeLastProvider then
                match taggedKeySets.TryGetValue lang with
                | true, tagged when tagged.Remove key ->
                    match localisationKeySets |> Map.tryFind lang with
                    | Some current ->
                        let updated = Set.remove key current
                        localisationKeySets <-
                            if updated.IsEmpty then Map.remove lang localisationKeySets
                            else Map.add lang updated localisationKeySets
                    | None -> ()
                    if tagged.Count = 0 then taggedKeySets.Remove lang |> ignore
                | _ -> ()

    let publishLocalisationKeys () =
        this.localisationKeys <-
            localisationKeySets |> Map.toArray

        this.taggedLocalisationKeys <-
            taggedKeySets
            |> Seq.map (fun pair ->
                pair.Key, pair.Value)
            |> Seq.sortBy (fun (lang, _) -> lang.ToString())
            |> Seq.toArray

    let tryEffectiveValidatableEntry
        (sourceMap: Map<string * Lang, struct (bool * ILocalisationAPI)>)
        lang
        key
        =
        let mutable result = None
        for KeyValue((_, candidateLang), struct (validate, api)) in sourceMap do
            if validate && candidateLang = lang then
                match api.ValueMap |> Map.tryFind key with
                | Some entry -> result <- Some entry
                | None -> ()
        result

    let processedMapFor lang =
        lookup.proccessedLoc
        |> List.tryPick (fun (candidateLang, entries) -> if candidateLang = lang then Some entries else None)
        |> Option.defaultValue Map.empty

    let removeProcessedSourceReferences lang sourceKey =
        let source = struct (lang, sourceKey)
        match processedReferencesBySource.TryGetValue source with
        | true, references ->
            for reference in references do
                let reverseKey = struct (lang, reference)
                match processedSourcesByReference.TryGetValue reverseKey with
                | true, sources ->
                    sources.Remove sourceKey |> ignore
                    if sources.Count = 0 then processedSourcesByReference.Remove reverseKey |> ignore
                | false, _ -> ()
            processedReferencesBySource.Remove source |> ignore
        | false, _ -> ()

    let addProcessedSourceReferences lang sourceKey (entry: LocEntry) =
        let references = entry.refs |> List.distinct |> List.toArray
        if references.Length > 0 then
            processedReferencesBySource.[struct (lang, sourceKey)] <- references
            for reference in references do
                let reverseKey = struct (lang, reference)
                let sources =
                    match processedSourcesByReference.TryGetValue reverseKey with
                    | true, existing -> existing
                    | false, _ ->
                        let created = HashSet<string>(StringComparer.Ordinal)
                        processedSourcesByReference.Add(reverseKey, created)
                        created
                sources.Add sourceKey |> ignore

    let rebuildProcessedReferenceIndex () =
        processedReferencesBySource.Clear()
        processedSourcesByReference.Clear()
        for lang, entries in lookup.proccessedLoc do
            for KeyValue(sourceKey, entry) in entries do
                addProcessedSourceReferences lang sourceKey entry

    let mergePendingDelta (delta: LocalisationDelta) =
        pendingDelta <-
            match pendingDelta with
            | None -> Some delta
            | Some current ->
                Some
                    { changedKeys = Array.append current.changedKeys delta.changedKeys |> Array.distinct
                      affectedLocalisationFiles =
                        Array.append current.affectedLocalisationFiles delta.affectedLocalisationFiles
                        |> Array.distinct
                      semanticChanged = current.semanticChanged || delta.semanticChanged }

    let updateAllLocalisationSources () =
        localisationAPIMap <-
            let allLocs =
                resources.GetResources()
                |> List.choose (function
                    | FileWithContentResource(_, e) -> Some e
                    | _ -> None)
                |> PSeq.choose parseLocFile
                |> Seq.collect id

            allLocs |> Map.ofSeq

        duplicateLocalisationKeyCounts.Clear()
        localisationKeySets <- Map.empty
        taggedKeySets.Clear()
        for struct (_, api) in localisationAPIMap.Values do
            addKeys api.GetLang api.GetKeys
        publishLocalisationKeys ()

    let updateLocalisationSource (locFile: FileWithContentResource) =
        let loc = parseLocFile locFile |> Option.defaultValue [||]

        let oldApis =
            localisationAPIMap
            |> Map.toArray
            |> Array.choose (fun ((filepath, lang), struct (_, api)) ->
                if filepath = locFile.filepath then Some(lang, api) else None)

        let changedByLanguage = Dictionary<Lang, HashSet<string>>()
        let addChanged lang (keys: seq<string>) =
            let changed =
                match changedByLanguage.TryGetValue lang with
                | true, existing -> existing
                | false, _ ->
                    let created = HashSet<string>(StringComparer.Ordinal)
                    changedByLanguage.Add(lang, created)
                    created
            changed.UnionWith keys

        for lang, api in oldApis do addChanged lang api.GetKeys
        for (_, lang), struct (_, api) in loc do addChanged lang api.GetKeys

        let oldEffective = Dictionary<struct (Lang * string), Entry option>()
        for KeyValue(lang, changed) in changedByLanguage do
            for key in changed do
                oldEffective.[struct (lang, key)] <- tryEffectiveValidatableEntry localisationAPIMap lang key

        // First remove all existing entries for this file (across all languages)
        // to prevent stale entries from accumulating when a file is re-parsed
        let cleanedMap =
            localisationAPIMap
            |> Map.filter (fun (fp, _) _ -> fp <> locFile.filepath)

        let newMap =
            loc
            |> Array.fold (fun map (key, value) -> Map.add key value map) cleanedMap

        for lang, api in oldApis do removeKeys lang api.GetKeys
        for (_, lang), struct (_, api) in loc do addKeys lang api.GetKeys
        localisationAPIMap <- newMap
        publishLocalisationKeys ()

        let processLoc = processLocalisation lookup
        let affectedSourceKeys = Dictionary<Lang, HashSet<string>>()
        let affectedFiles = HashSet<string>(pathComparer)
        affectedFiles.Add locFile.filepath |> ignore
        let changedKeys = HashSet<string>(StringComparer.Ordinal)
        let mutable semanticChanged = false

        let addAffectedSource lang key =
            let keys =
                match affectedSourceKeys.TryGetValue lang with
                | true, existing -> existing
                | false, _ ->
                    let created = HashSet<string>(StringComparer.Ordinal)
                    affectedSourceKeys.Add(lang, created)
                    created
            keys.Add key |> ignore

        for KeyValue(lang, changed) in changedByLanguage do
            let oldProcessed = processedMapFor lang
            let mutable newProcessed = oldProcessed
            let additions = ResizeArray<string * Entry>()

            for key in changed do
                changedKeys.Add key |> ignore
                let oldEntry = oldEffective.[struct (lang, key)]
                let newEntry = tryEffectiveValidatableEntry localisationAPIMap lang key
                if oldEntry <> newEntry then
                    semanticChanged <- true
                    addAffectedSource lang key
                    match processedSourcesByReference.TryGetValue(struct (lang, key)) with
                    | true, sources -> for source in sources do addAffectedSource lang source
                    | false, _ -> ()
                    match newEntry with
                    | Some entry -> additions.Add(key, entry)
                    | None -> newProcessed <- Map.remove key newProcessed

            if additions.Count > 0 then
                let processedAdditions =
                    additions
                    |> Seq.map (fun (key, entry) -> key, entry)
                    |> Map.ofSeq
                    |> fun entries -> processLoc (lang, entries)
                    |> snd
                newProcessed <- Map.fold (fun state key entry -> Map.add key entry state) newProcessed processedAdditions

            if not (Object.ReferenceEquals(oldProcessed, newProcessed)) then
                lookup.proccessedLoc <-
                    let mutable replaced = false
                    let updated =
                        lookup.proccessedLoc
                        |> List.map (fun (candidateLang, entries) ->
                            if candidateLang = lang then
                                replaced <- true
                                candidateLang, newProcessed
                            else
                                candidateLang, entries)
                    if replaced then updated else (lang, newProcessed) :: updated

            match affectedSourceKeys.TryGetValue lang with
            | true, sources ->
                for sourceKey in sources |> Seq.toArray do
                    removeProcessedSourceReferences lang sourceKey
                    match Map.tryFind sourceKey newProcessed with
                    | Some entry ->
                        addProcessedSourceReferences lang sourceKey entry
                        affectedFiles.Add entry.position.FileName |> ignore
                    | None ->
                        match Map.tryFind sourceKey oldProcessed with
                        | Some entry -> affectedFiles.Add entry.position.FileName |> ignore
                        | None -> ()
            | false, _ -> ()

        let delta =
            { changedKeys = changedKeys |> Seq.toArray
              affectedLocalisationFiles = affectedFiles |> Seq.toArray
              semanticChanged = semanticChanged }
        mergePendingDelta delta

    let updateProcessedLocalisation () =
        let validatableEntries =
            validatableLocalisation ()
            |> List.groupBy _.GetLang
            |> List.map (fun (k, g) ->
                k,
                g
                |> Seq.collect (fun ls -> ls.GetEntries |> Seq.map (fun x -> (x.key, x)))
                |> Map.ofSeq)

        let processLoc = processLocalisation lookup
        lookup.proccessedLoc <- validatableEntries |> List.map processLoc
        rebuildProcessedReferenceIndex ()
        pendingDelta <- None

    member val localisationErrors: CWError list option = None with get, set
    member val globalLocalisationErrors: CWError list option = None with get, set
    member val localisationKeys: (Lang * Set<string>) array = [||] with get, set
    member val taggedLocalisationKeys: (Lang * LocKeySet) array = [||] with get, set

    member this.UpdateAllLocalisation() =
        updateAllLocalisationSources ()
        updateProcessedLocalisation ()

    member _.UpdateProcessedLocalisation() = updateProcessedLocalisation ()
    member _.UpdateLocalisationFile(locFile: FileWithContentResource) = updateLocalisationSource locFile

    member _.TakeDelta() =
        let result = pendingDelta
        pendingDelta <- None
        result

    member _.ProcessedLocalisationForFiles(files: Set<string>) =
        lookup.proccessedLoc
        |> List.map (fun (lang, entries) ->
            lang,
            entries
            |> Map.filter (fun _ entry -> files.Contains entry.position.FileName))
        |> List.filter (fun (_, entries) -> not entries.IsEmpty)

    member _.GetLocalisationAPIsForFiles(files: Set<string>) =
        localisationAPIMap
        |> Map.toSeq
        |> Seq.choose (fun ((filepath, _), struct (validate, api)) ->
            if files.Contains filepath then Some(struct (validate, api)) else None)
        |> Seq.toList

    member _.ApplyIncrementalErrors(files: Set<string>, localErrors: CWError list, globalErrors: CWError list) =
        let replaceAffected (existing: CWError list option) (replacements: CWError list) =
            existing
            |> Option.defaultValue []
            |> List.filter (fun error -> not (files.Contains error.range.FileName))
            |> fun retained -> retained @ replacements

        this.localisationErrors <- Some(replaceAffected this.localisationErrors localErrors)
        this.globalLocalisationErrors <- Some(replaceAffected this.globalLocalisationErrors globalErrors)

    member _.GetLocalisationAPIs() : (struct (bool * ILocalisationAPI)) list = localisationAPIMap.Values |> Seq.toList

    member this.GetCleanLocalisationAPIs() : ILocalisationAPI seq =
        localisationAPIMap.Values |> Seq.map structSnd

    member _.LocalisationFileNames() : string list =
        localisationAPIMap
        |> Map.toList
        |> List.map (fun ((f, l), (_, a)) -> sprintf "%A, %s, %i" l f a.GetKeys.Length)

    member this.LocalisationKeys() = this.localisationKeys

    member this.LocalisationEntries() : (Lang * struct (string * Entry) array) seq =
        this.GetCleanLocalisationAPIs()
        |> Seq.groupBy _.GetLang
        |> Seq.map (fun (k, g) ->
            k,
            g
            |> Seq.collect (fun ls -> ls.GetEntries |> Seq.map (fun x -> struct (x.key, x)))
            |> Seq.toArray)
