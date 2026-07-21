namespace CWTools.Utilities

open System
open System.Buffers
open System.Collections.Concurrent
open System.Collections.Frozen
open System.Collections.Generic
open System.Linq
open System.Runtime.CompilerServices
open System.Runtime.Serialization
open System.Threading
open CWTools.Utilities.Position
open System.Globalization
open System.IO
open KTrie

module Utils =


    let inline (==) (x: string) (y: string) =
        x.Equals(y, StringComparison.OrdinalIgnoreCase)

    type LocKeySet = HashSet<string>

    type LogLevel =
        | Silent
        | Normal
        | Verbose


    /// For the default logger only
    let mutable loglevel = Silent

    let logInner level message =
        match loglevel, level with
        | Silent, _ -> ()
        | Normal, Normal -> Printf.eprintfn "%s: %s" (System.DateTime.Now.ToString("HH:mm:ss")) message
        | Verbose, _ -> Printf.eprintfn "%s: %s" (System.DateTime.Now.ToString("HH:mm:ss")) message
        | _, _ -> ()
    // |Verbose -> logWith logger format

    let private defaultLogVerbose message = logInner Verbose message
    let private defaultLogNormal message = logInner Normal message

    let private defaultLogAll message =
        Printf.eprintfn "%s: %s" (System.DateTime.Now.ToString("HH:mm:ss")) message

    let mutable logDiag = defaultLogVerbose
    let mutable logInfo = defaultLogNormal
    let mutable logWarning = defaultLogNormal
    let mutable logError = defaultLogAll

    let log m = logInfo m

    let duration f s =
        // let timer = new System.Diagnostics.Stopwatch()
        // timer.Start()
        let returnValue = f ()
        //log (sprintf "Elapsed Time: %i %s" timer.ElapsedMilliseconds s)
        returnValue

    let mkZeroFile file =
        mkRange file (mkPos 0 0) (mkPos 10000 0)



    let repeatN f n x =
        let mutable x = x

        for i = 1 to n do
            x <- f x

        x

    let structSnd struct (_, x) = x
    let structFst struct (x, _) = x

    [<Literal>]
    let magicChar = '\u1E00'

    [<Literal>]
    let magicCharString = "\u1E00"

    let quoteChar = '"'

module TryParser =
    // convenient, functional TryParse wrappers returning option<'a>
    let tryParseWith tryParseFunc =
        tryParseFunc
        >> function
            | true, v -> ValueSome v
            | false, _ -> ValueNone

    let parseDate: string -> _ = tryParseWith DateTime.TryParse
    let parseInt: string -> _ = tryParseWith Int32.TryParse
    let parseIntSpan (s: ReadOnlySpan<char>)  =
        match Int32.TryParse(s) with
        | true, v -> ValueSome v
        | false, _ -> ValueNone

    let parseIntWithDecimal: string -> _ =
        tryParseWith (fun s ->
            System.Int32.TryParse(
                s,
                Globalization.NumberStyles.AllowDecimalPoint
                ||| Globalization.NumberStyles.Integer,
                CultureInfo.InvariantCulture
            ))

    let parseInt64: string -> _ =
        tryParseWith (fun s -> Int64.TryParse(s, NumberStyles.Integer, CultureInfo.InvariantCulture))

    let parseInt64Span (s: ReadOnlySpan<char>) =
        match Int64.TryParse(s, NumberStyles.Integer, CultureInfo.InvariantCulture) with
        | true, v -> ValueSome v
        | false, _ -> ValueNone

    let parseInt64WithDecimal: string -> _ =
        tryParseWith (fun s ->
            Int64.TryParse(
                s,
                Globalization.NumberStyles.AllowDecimalPoint ||| Globalization.NumberStyles.Integer,
                CultureInfo.InvariantCulture
            ))

    let parseSingle: string -> _ = tryParseWith System.Single.TryParse

    let parseDouble: string -> _ =
        tryParseWith (fun s ->
            System.Double.TryParse(
                s,
                (Globalization.NumberStyles.Float ||| Globalization.NumberStyles.AllowThousands),
                CultureInfo.InvariantCulture
            ))

    let parseDecimal: string -> _ =
        tryParseWith (fun s ->
            Decimal.TryParse(s, (NumberStyles.Float ||| NumberStyles.AllowThousands), CultureInfo.InvariantCulture))

    let parseDecimalSpan (s: ReadOnlySpan<char>) =
        match
            Decimal.TryParse(s, (NumberStyles.Float ||| NumberStyles.AllowThousands), CultureInfo.InvariantCulture)
        with
        | true, v -> ValueSome v
        | false, _ -> ValueNone


    // etc.

    // active patterns for try-parsing strings
    let (|Date|_|) = parseDate
    let (|Int|_|) = parseInt
    let (|Single|_|) = parseSingle
    let (|Double|_|) = parseDouble


type StringToken = int
type StringLowerToken = int

[<Struct; IsReadOnly>]
type StringTokens =
    val lower: StringLowerToken
    val normal: StringToken
    /// We throw away the quotes when we intern, but we do need to keep that info, but don't want to have multiple tokens with/without quotes
    val quoted: bool

    new(lower, normal, quoted) =
        { lower = lower
          normal = normal
          quoted = quoted }

[<Struct; IsReadOnly>]
type StringMetadata =
    val startsWithAmp: bool
    val containsDoubleDollar: bool
    val containsQuestionMark: bool
    val containsHat: bool
    val startsWithSquareBracket: bool
    val containsPipe: bool

    new(startsWithAmp, containsDoubleDollar, containsQuestionMark, containsHat, startsWithSquareBracket, containsPipe) =
        { startsWithAmp = startsWithAmp
          containsDoubleDollar = containsDoubleDollar
          containsQuestionMark = containsQuestionMark
          containsHat = containsHat
          startsWithSquareBracket = startsWithSquareBracket
          containsPipe = containsPipe }

[<Sealed>]
type StringResourceManager() =
    // TODO: Replace with arrays?
    let strings = new ConcurrentDictionary<string, StringTokens>()
    let ints = new ConcurrentDictionary<StringToken, string>()
    let metadata = new ConcurrentDictionary<StringToken, StringMetadata>()
    [<NonSerialized>]
    let mutable internLocks = Array.init 64 (fun _ -> obj ())

    let mutable i = 0

    let addData (key: string) (ls: string) =
        let quoted = key.StartsWith '\"' && key.EndsWith '\"'

        match strings.TryGetValue(ls) with
        | true, existingLower ->
            let stringID = Interlocked.Increment(&i) - 1
            let newToken = StringTokens(existingLower.lower, stringID, quoted)
            ints[stringID] <- key
            metadata[stringID] <- metadata[existingLower.lower]
            newToken
        | false, _ ->
            let stringID = Interlocked.Add(&i, 2) - 2
            let lowID = stringID + 1

            let tokenMetadata =
                if ls.Length > 0 then
                    let startsWithAmp = ls[0] = '@'
                    let containsQuestionMark = ls.IndexOf('?') >= 0
                    let containsHat = ls.IndexOf('^') >= 0
                    let first = ls.IndexOf('$')
                    let last = ls.LastIndexOf('$')
                    let containsDoubleDollar = first >= 0 && first <> last
                    let startsWithSquareBracket = ls[0] = '[' || ls[0] = ']'
                    let containsPipe = ls.IndexOf('|') >= 0

                    StringMetadata(
                        startsWithAmp,
                        containsDoubleDollar,
                        containsQuestionMark,
                        containsHat,
                        startsWithSquareBracket,
                        containsPipe
                    )
                else
                    StringMetadata(false, false, false, false, false, false)

            let normalToken = StringTokens(lowID, stringID, quoted)
            let lowerToken = StringTokens(lowID, lowID, false)

            ints[lowID] <- ls
            ints[stringID] <- key
            metadata[lowID] <- tokenMetadata
            metadata[stringID] <- tokenMetadata

            strings.TryAdd(ls, lowerToken) |> ignore

            normalToken

    [<OnDeserialized>]
    member _.OnDeserialized(_context: StreamingContext) =
        internLocks <- Array.init 64 (fun _ -> obj ())

    member _.InternIdentifierToken(s: string) : StringTokens =
        match strings.TryGetValue(s) with
        | true, token -> token
        | false, _ ->
            let lower = s.ToLower().Trim('"')
            let hash = StringComparer.Ordinal.GetHashCode(lower) &&& Int32.MaxValue

            lock internLocks[hash % internLocks.Length] (fun () ->
                match strings.TryGetValue(s) with
                | true, token -> token
                | false, _ ->
                    let candidate = addData s lower

                    if strings.TryAdd(s, candidate) then
                        candidate
                    else
                        strings[s])

    member x.GetStringForIDs(id: StringTokens) = ints[id.normal]
    member x.GetLowerStringForIDs(id: StringTokens) = ints[id.lower]
    member x.GetStringForID(id: StringToken) = ints[id]
    member x.GetMetadataForID(id: StringToken) = metadata[id]

    /// Diagnostic: number of unique interned string forms (case-sensitive keys in `strings` dict)
    member _.StringCount = strings.Count
    /// Diagnostic: total int→string mappings (normal + lower IDs)
    member _.IntCount = ints.Count
    /// Diagnostic: current monotonic token ID counter
    member _.TokenIdCounter = i

module StringResource =
    let mutable stringManager = StringResourceManager()

type StringTokens with

    member this.GetString() =
        StringResource.stringManager.GetStringForIDs this

    member this.GetMetadata() =
        StringResource.stringManager.GetMetadataForID this.normal

module Utils2 =

    [<Sealed>]
    type private CharacterComparer() =
        static member Default = CharacterComparer()

        interface IEqualityComparer<char> with
            member _.Equals(x, y) =
                if x = y then true
                else if Char.IsUpper y then Char.ToUpperInvariant x = y
                else Char.ToLowerInvariant x = y

            member _.GetHashCode(c) = c.GetHashCode()

    [<Sealed>]
    type LowerStringSparseTrie() =
        let trie = Trie(CharacterComparer.Default)

        let idValueList = ResizeArray<StringTokens>()

        member this.Contains(key: string) =
            if key <> "" then trie.Contains key else false

        member this.Contains(key: ReadOnlySpan<char>) =
            if not key.IsEmpty then trie.Contains key else false

        member this.LongestPrefixMatch(input: ReadOnlySpan<char>) : string | null =
            if not input.IsEmpty then
                trie.LongestPrefixMatch input
            else
                null

        member this.FindFirstByPrefix(input: ReadOnlySpan<char>) : string | null =
            if not input.IsEmpty then
                (trie.EnumerateByPrefix input).FirstOrDefault()
            else
                null

        member this.AddWithIDs(value: string) =
            if value <> "" then
                trie.Add(value) |> ignore
                idValueList.Add(StringResource.stringManager.InternIdentifierToken value)

        member this.Add(value: string) =
            if value <> "" then
                trie.Add(value) |> ignore

        member this.Count = trie.Count
        member _.IdValues = idValueList

        member _.StringValues =
            idValueList |> Seq.map (fun i -> StringResource.stringManager.GetStringForIDs i)

        member _.IdCount = idValueList.Count

    type PrefixOptimisedStringSet = LowerStringSparseTrie

    [<Sealed>]
    type IgnoreCaseStringSet(strings: string seq) =
        let mutable set = null

        do set <- strings.ToFrozenSet(StringComparer.OrdinalIgnoreCase)

        new() = IgnoreCaseStringSet(Seq.empty)

        member this.Contains(x: string) = set.Contains(x)

    let createStringSet (items: string seq) =
        let newSet = PrefixOptimisedStringSet()

        match items with
        | :? (string array) as array -> array |> Array.iter newSet.AddWithIDs
        | _ -> items |> Seq.iter newSet.AddWithIDs

        newSet

/// Bounded nearest-name lookup used to append "did you mean X?" suggestions to
/// validation error messages. Kept deliberately cheap: it only runs on error
/// paths, scans a capped number of candidates, and abandons distance
/// computations as soon as they exceed the current best.
module NameSuggestion =

    /// Upper bound on candidates scanned per suggestion, so huge sets
    /// (e.g. all localisation keys) cannot make error reporting slow.
    [<Literal>]
    let private MaxCandidates = 20000

    let private maxDistanceFor (length: int) =
        if length <= 6 then 1
        elif length <= 12 then 2
        else 3

    let private levenshteinWithinBuffers
        (maxDist: int)
        (a: string)
        (b: string)
        (prev: int array)
        (curr: int array)
        =
        if maxDist < 0 || abs (a.Length - b.Length) > maxDist then
            ValueNone
        else
            let la, lb = a.Length, b.Length
            for j in 0..lb do
                prev.[j] <- j

            let mutable prev = prev
            let mutable curr = curr
            let mutable exceeded = false
            let mutable i = 1

            while not exceeded && i <= la do
                curr.[0] <- i
                let mutable rowMin = i
                let ca = Char.ToLowerInvariant a.[i - 1]

                for j in 1..lb do
                    let cost = if ca = Char.ToLowerInvariant b.[j - 1] then 0 else 1
                    let v = min (min (curr.[j - 1] + 1) (prev.[j] + 1)) (prev.[j - 1] + cost)
                    curr.[j] <- v
                    if v < rowMin then rowMin <- v

                if rowMin > maxDist then exceeded <- true
                let tmp = prev
                prev <- curr
                curr <- tmp
                i <- i + 1

            if exceeded then ValueNone
            else if prev.[lb] <= maxDist then ValueSome prev.[lb]
            else ValueNone

    /// Case-insensitive Levenshtein distance with a cutoff: ValueNone if the
    /// distance exceeds maxDist (computation stops early when it must).
    let levenshteinWithin (maxDist: int) (a: string) (b: string) =
        if maxDist < 0 || abs (a.Length - b.Length) > maxDist then
            ValueNone
        else
            let rowLength = b.Length + 1
            let prev = ArrayPool<int>.Shared.Rent rowLength
            let curr = ArrayPool<int>.Shared.Rent rowLength

            try
                levenshteinWithinBuffers maxDist a b prev curr
            finally
                ArrayPool<int>.Shared.Return prev
                ArrayPool<int>.Shared.Return curr

    /// The closest candidate within an edit-distance budget scaled by the
    /// value's length, or None. Values shorter than 4 chars are skipped (too noisy).
    let suggestClosest (value: string) (candidates: string seq) : string option =
        if isNull value || value.Length < 4 then
            None
        else
            let maxDist = maxDistanceFor value.Length
            let mutable best: string option = None
            let mutable bestDist = maxDist + 1
            let mutable scanned = 0
            let maxRowLength = value.Length + maxDist + 1
            let prev = ArrayPool<int>.Shared.Rent maxRowLength
            let curr = ArrayPool<int>.Shared.Rent maxRowLength

            try
                use e = candidates.GetEnumerator()

                while bestDist > 1 && scanned < MaxCandidates && e.MoveNext() do
                    let candidate = e.Current
                    scanned <- scanned + 1

                    if not (isNull candidate) && candidate.Length > 0 then
                        match levenshteinWithinBuffers (bestDist - 1) value candidate prev curr with
                        | ValueSome d when d >= 1 ->
                            bestDist <- d
                            best <- Some candidate
                        | _ -> ()

                best
            finally
                ArrayPool<int>.Shared.Return prev
                ArrayPool<int>.Shared.Return curr

    /// Formats " (did you mean 'x'?)" for appending to an error message, or "".
    let didYouMean (value: string) (candidates: string seq) =
        match suggestClosest value candidates with
        | Some s -> $" (did you mean '%s{s}'?)"
        | None -> ""
