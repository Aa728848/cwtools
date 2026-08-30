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
