module MemoryLifecycleTests

open System
open System.IO
open System.Threading
open System.Threading.Tasks
open Expecto
open TestHelpers
open LogCaptureTest
open CWTools.Games
open CWTools.Games.Stellaris

let private cacheValue = Map.ofList [ "effect", [ "param" ] ]

let private populate path source =
    LanguageFeatures.getOrBuildScriptedEffectParamMapCacheValue path source (fun () -> cacheValue)
    |> ignore

let private smallGame () =
    let folder = Path.GetFullPath "./testfiles/localisationtests/gamefiles"
    STLGame(emptyStellarisSettings folder) :> IGame<_>, folder

[<Tests>]
let scriptedEffectParamMapCacheTests =
    testList "scripted effect parameter cache lifecycle" [
        test "path aliases share one OS-correct cache entry" {
            LanguageFeatures.clearScriptedEffectParamMapCache ()
            let source = obj ()
            let absolute = Path.GetFullPath(Path.Combine(".", "cache-tests", "effect.txt"))
            let alias = Path.Combine(Path.GetDirectoryName absolute, ".", Path.GetFileName absolute)
            populate absolute source
            populate alias source
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheCount ()) 1 "absolute aliases must collapse"
            if OperatingSystem.IsWindows() then
                populate (absolute.ToUpperInvariant()) source
                Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheCount ()) 1 "Windows aliases are case-insensitive"
        }

        test "concurrent inserts never exceed hard maximum and build once per key" {
            LanguageFeatures.clearScriptedEffectParamMapCache ()
            let builds = ref 0
            let sharedSource = obj ()
            let sharedPath = Path.GetFullPath "./cache-tests/shared.txt"
            Parallel.For(0, 64, fun _ ->
                LanguageFeatures.getOrBuildScriptedEffectParamMapCacheValue sharedPath sharedSource (fun () ->
                    Interlocked.Increment builds |> ignore
                    cacheValue) |> ignore) |> ignore
            Expect.equal builds.Value 1 "one key must have one published build"

            Parallel.For(0, 1024, fun index ->
                let path = Path.GetFullPath(sprintf "./cache-tests/%04d.txt" index)
                populate path (obj ())) |> ignore
            Expect.isLessThanOrEqual (LanguageFeatures.scriptedEffectParamMapCacheCount ()) LanguageFeatures.ScriptedEffectParamMapCacheMaxEntries "concurrent inserts must obey the hard bound"
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheBookkeepingCount ()) (LanguageFeatures.scriptedEffectParamMapCacheCount ()) "bookkeeping must contain exactly one node per live entry"
        }

        test "repeated replacements keep bookkeeping strictly bounded" {
            LanguageFeatures.clearScriptedEffectParamMapCache ()
            let paths = [| for index in 0 .. 3 -> Path.GetFullPath(sprintf "./cache-tests/replaced-%d.txt" index) |]
            Parallel.For(0, 4096, fun index -> populate paths.[index % paths.Length] (obj ())) |> ignore
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheCount ()) paths.Length "replacement retains one value per key"
            Expect.isLessThanOrEqual (LanguageFeatures.scriptedEffectParamMapCacheBookkeepingCount ()) LanguageFeatures.ScriptedEffectParamMapCacheMaxEntries "replacement bookkeeping must obey the 256-entry hard bound"
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheBookkeepingCount ()) paths.Length "replacement bookkeeping is strictly bounded by live keys"
        }

        testWithCapturedLogs "edit delete and full refresh invalidate entries" <| fun () ->
            LanguageFeatures.clearScriptedEffectParamMapCache ()
            let game, folder = smallGame ()
            let file = Path.GetFullPath(Path.Combine(folder, "events", "test_events.txt"))
            let deleteFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
            let text = File.ReadAllText file

            populate file (obj ())
            game.UpdateFile true file (Some text) |> ignore
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheCount ()) 0 "edit removes the file entry"

            populate deleteFile (obj ())
            let incremental = game :?> IIncrementalTypeIndex
            incremental.RemoveTypeIndex [ deleteFile ] |> ignore
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheCount ()) 0 "delete removes the file entry"

            populate file (obj ())
            game.RefreshCaches()
            Expect.equal (LanguageFeatures.scriptedEffectParamMapCacheCount ()) 0 "full refresh clears all entries"
    ]

[<Tests>]
let preparedTypeIndexServiceCacheTests =
    testList "prepared type-index service cache lifecycle" [
        testWithCapturedLogs "full refresh and rejected staged refresh cannot retain a prepared service" <| fun () ->
            let game, folder = smallGame ()
            let file = Path.GetFullPath(Path.Combine(folder, "events", "test_events.txt"))
            let index = game :?> IIncrementalTypeIndex

            index.PrepareTypeIndex [ file ] |> ignore
            index.PrepareTypeIndex [ file ] |> ignore
            let staged = game.PrepareRefreshCaches().Value
            game.RefreshCaches()
            Expect.isFalse (game.CommitRefreshCaches staged) "stale staged refresh is rejected"
            index.PrepareTypeIndex [ file ] |> ignore

            let rec findManager depth (value: obj) =
                if depth < 0 || isNull value then None
                else
                    let methodInfo = value.GetType().GetMethod("PreparedTypeIndexServiceCacheStats", Reflection.BindingFlags.Instance ||| Reflection.BindingFlags.NonPublic)
                    if not (isNull methodInfo) then Some(value, methodInfo)
                    else
                        value.GetType().GetFields(Reflection.BindingFlags.Instance ||| Reflection.BindingFlags.NonPublic)
                        |> Array.tryPick (fun field -> findManager (depth - 1) (field.GetValue value))
            let manager = findManager 3 game
            Expect.isSome manager "test fixture exposes its internal rules manager"
            let target, statsMethod = manager.Value
            let cached, hits, misses = statsMethod.Invoke(target, [||]) :?> (bool * int64 * int64)
            Expect.isTrue cached "post-refresh prepare publishes a fresh service"
            Expect.isGreaterThanOrEqual hits 1L "second prepare hit the pre-refresh cache"
            Expect.isGreaterThanOrEqual misses 2L "post-refresh prepare missed instead of reusing stale service"
    ]

/// Locate an internal stats method (declared on the game or one of its managers) and
/// return the owning object together with the MethodInfo so tests can invoke it.
let private tryFindStatsMethod (names: string list) (value: obj) =
    let rec find depth (current: obj) =
        if depth < 0 || isNull current then
            None
        else
            let methods =
                current.GetType().GetMethods(
                    Reflection.BindingFlags.Instance
                    ||| Reflection.BindingFlags.NonPublic
                    ||| Reflection.BindingFlags.Public
                )

            let direct =
                names |> List.tryPick (fun name -> methods |> Array.tryFind (fun m -> m.Name = name))

            match direct with
            | Some m -> Some(current, m)
            | None ->
                current.GetType().GetFields(Reflection.BindingFlags.Instance ||| Reflection.BindingFlags.NonPublic)
                |> Array.tryPick (fun field -> find (depth - 1) (field.GetValue current))

    find 8 value

let private invokeInt64Stats (target: obj, methodInfo: Reflection.MethodInfo) : int64 * int64 =
    methodInfo.Invoke(target, [||]) :?> (int64 * int64)

[<Tests>]
let serviceInputCacheObservationTests =
    testList "service input cache reference-keyed reuse" [
        test "unchanged sources are reused and changed sources recompute" {
            let game, _folder = smallGame ()

            let serviceInputStats () =
                match tryFindStatsMethod [ "ServiceInputCacheStats" ] game with
                | Some pair -> invokeInt64Stats pair
                | None -> failwith "game should expose ServiceInputCacheStats"

            let hits0, misses0 = serviceInputStats ()
            game.RefreshCaches ()
            let hits1, misses1 = serviceInputStats ()
            Expect.isGreaterThan misses1 misses0 "initial refresh materializes the service inputs"

            game.RefreshCaches ()
            let hits2, misses2 = serviceInputStats ()
            Expect.isGreaterThan hits2 hits1 "unchanged config rules must reuse the cached rules wrapper"
            Expect.isGreaterThan misses2 misses1 "rebuilt var/type/enum maps must recompute after a refresh"

            // A brand new rules source reference must never hit the stale cached wrapper.
            game.ReplaceConfigRules []
            game.RefreshCaches ()
            let _, misses3 = serviceInputStats ()
            Expect.isGreaterThan misses3 misses2 "a changed source reference must recompute instead of reusing stale inputs"
        }
    ]

[<Tests>]
let stagedProcessedLocalisationTests =
    testList "staged processed-localisation candidate lifecycle" [
        testWithCapturedLogs "stale localisation stage is rejected without publishing or touching the journal" <| fun () ->
            let game, folder = smallGame ()
            // Only English is configured for this fixture, so the probe key must be
            // written to an English source file for its keys to be tracked at all.
            let locFile = Path.GetFullPath(Path.Combine(folder, "localisation", "test_not_bom_l_english.yml"))
            let original = File.ReadAllText locFile
            let edited =
                original
                + Environment.NewLine
                + "  staged_reject_probe:0 \"[defined_event.NotReal]\""
                + Environment.NewLine

            let processedLocStats () =
                match tryFindStatsMethod [ "ProcessedLocalisationCommandStats" ] game with
                | Some pair -> invokeInt64Stats pair
                | None -> failwith "game should expose ProcessedLocalisationCommandStats"

            let pendingProbeKeys () =
                let incremental = game :?> IIncrementalLocalisation
                match incremental.PeekLocalisationDelta "staged-processed-loc-test" with
                | Ok(Some detached) -> detached.delta.changedKeys
                | Ok None -> [||]
                | Error error -> failwithf "peek localisation delta failed: %A" error

            let staged = game.PrepareRefreshCaches().Value
            game.UpdateFile true locFile (Some edited) |> ignore
            Expect.isFalse (game.CommitRefreshCaches staged) "stale localisation stage must be rejected"
            let _, commitsAfterReject = processedLocStats ()
            Expect.equal commitsAfterReject 0L "rejected stage must not publish the processed-localisation candidate"
            // Publishing makes the localisation caches visible to incremental readers.
            game.LocalisationErrors(true, true) |> ignore
            Expect.contains (pendingProbeKeys ()) "staged_reject_probe" "rejected stage must leave the delta journal untouched"

            let staged2 = game.PrepareRefreshCaches().Value
            Expect.isTrue (game.CommitRefreshCaches staged2) "fresh stage prepared after the edit must commit"
            let prepares, commits = processedLocStats ()
            Expect.isGreaterThanOrEqual prepares 2L "each prepare builds a processed-localisation candidate"
            Expect.equal commits 1L "only the guarded stage publishes its candidate"
            Expect.contains (pendingProbeKeys ()) "staged_reject_probe" "commit must not clear or acknowledge the delta journal"

        testWithCapturedLogs "staged commit matches legacy refresh for CW226 diagnostics and the delta journal" <| fun () ->
            // Only English is configured for this fixture, so the probe key must be
            // written to an English source file for its keys to be tracked at all.
            let locRelativePath = Path.Combine("localisation", "test_not_bom_l_english.yml")
            let editedSuffix =
                Environment.NewLine
                + "  equivalence_probe:0 \"[defined_event.NotReal]\""
                + Environment.NewLine

            let buildObservations applyRefresh =
                let game, folder = smallGame ()
                let locFile = Path.GetFullPath(Path.Combine(folder, locRelativePath))
                let edited = File.ReadAllText locFile + editedSuffix
                game.UpdateFile true locFile (Some edited) |> ignore
                applyRefresh game

                let cw226 =
                    game.LocalisationErrors(true, true)
                    |> List.filter (fun error -> error.code = "CW226")
                    |> List.map (fun error -> error.range.FileName, error.message)
                    |> List.sort

                let incremental = game :?> IIncrementalLocalisation
                let delta =
                    match incremental.PeekLocalisationDelta "staged-equivalence-test" with
                    | Ok(Some detached) ->
                        Some(detached.delta.changedKeys |> Array.sort, detached.delta.semanticChanged)
                    | Ok None -> None
                    | Error error -> failwithf "peek localisation delta failed: %A" error

                cw226, delta

            let legacyCw226, legacyDelta =
                buildObservations (fun game -> game.RefreshCaches ())

            let stagedCw226, stagedDelta =
                buildObservations (fun game ->
                    let staged = game.PrepareRefreshCaches().Value
                    Expect.isTrue (game.CommitRefreshCaches staged) "staged commit must apply")

            Expect.equal stagedCw226 legacyCw226 "staged commit must produce the same CW226 diagnostics as the legacy refresh"
            Expect.equal stagedDelta legacyDelta "staged commit must leave the same pending delta journal as the legacy refresh"
    ]

[<Tests>]
let forceRecomputeLazyLifecycleTests =
    testList "force recompute keeps uncreated lazies and replaces created ones" [
        test "created lazies are replaced on demand while uncreated ones are kept" {
            let game, _folder = smallGame ()
            let snapshot () =
                game.AllEntities()
                |> Seq.map (fun struct (entity, data) -> entity.filepath, data)
                |> Seq.sortBy fst
                |> Seq.toArray

            let before = snapshot ()
            let uncreatedPath, uncreatedLazy =
                before |> Array.pick (fun (path, data) -> if not data.IsValueCreated then Some(path, data) else None)

            let createdPath, createdLazy =
                match before |> Array.tryFind (fun (_, data) -> data.IsValueCreated) with
                | Some pair -> pair
                | None ->
                    // Force a different entity than the preserved one: forcing the picked
                    // uncreated lazy itself would make ForceRecompute rightfully replace it.
                    let path, data =
                        before |> Array.find (fun (path, _) -> path <> uncreatedPath)

                    data.Force() |> ignore
                    path, data

            game.ForceRecompute ()

            let after = snapshot ()
            let uncreatedAfter = after |> Array.find (fun (path, _) -> path = uncreatedPath) |> snd
            let createdAfter = after |> Array.find (fun (path, _) -> path = createdPath) |> snd

            Expect.isTrue (obj.ReferenceEquals(uncreatedLazy, uncreatedAfter)) "uncreated lazy must keep its instance"
            Expect.isFalse uncreatedAfter.IsValueCreated "uncreated lazy must not be evaluated"
            Expect.isFalse (obj.ReferenceEquals(createdLazy, createdAfter)) "created lazy must be replaced"
            Expect.isFalse createdAfter.IsValueCreated "replaced lazy must not be prewarmed"
            let createdAfterCount = after |> Array.filter (fun (_, data) -> data.IsValueCreated) |> Array.length
            Expect.equal createdAfterCount 0 "force recompute must not prewarm the whole table"

            match tryFindStatsMethod [ "ForceRecomputeStats" ] game with
            | Some pair ->
                let replaced, skipped = invokeInt64Stats pair
                Expect.isGreaterThanOrEqual replaced 1L "at least the forced entity is replaced"
                Expect.isGreaterThanOrEqual skipped 1L "at least one uncreated entity keeps its instance"
            | None -> failwith "game should expose ForceRecomputeStats"
        }
    ]
