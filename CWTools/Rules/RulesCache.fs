namespace CWTools.Rules

open System
open System.IO
open System.IO.Compression
open System.Security.Cryptography
open MBrace.FsPickler
open CWTools.Common
open CWTools.Utilities.Position

type CachedCwtRulesData =
    { rules: RootRule array
      types: TypeDefinition list
      enums: EnumDefinition list
      complexenums: ComplexEnumDef list
      values: (string * string list) list
      metadata: ExtendedConfigMetadata }

type CachedDocsData =
    { triggers: DocEffect list
      effects: DocEffect list }

type CachedModifiersData =
    { modifiers: ActualModifier array }

module RulesCache =
    let mutable globalRulesCacheDir: string option = None

    let private cwdfMagic = [| 0x43uy; 0x57uy; 0x44uy; 0x46uy |] // ASCII "CWDF"

    let private binarySerializer =
        FsPickler.CreateBinarySerializer()

    let compressAndWrite (input: byte array) (file: string) =
        let dir = Path.GetDirectoryName file
        if not (String.IsNullOrEmpty dir) && not (Directory.Exists dir) then
            Directory.CreateDirectory dir |> ignore
        use fileStream = File.Create(file)
        fileStream.Write(cwdfMagic, 0, cwdfMagic.Length)
        use deflateStream = new DeflateStream(fileStream, CompressionLevel.Fastest)
        deflateStream.Write(input, 0, input.Length)

    let decompress (path: string) =
        let bytes = File.ReadAllBytes(path)
        if bytes.Length >= 4 && bytes.[0] = cwdfMagic.[0] && bytes.[1] = cwdfMagic.[1] && bytes.[2] = cwdfMagic.[2] && bytes.[3] = cwdfMagic.[3] then
            use inStream = new MemoryStream(bytes, 4, bytes.Length - 4)
            use deflateStream = new DeflateStream(inStream, CompressionMode.Decompress)
            use outStream = new MemoryStream()
            deflateStream.CopyTo(outStream)
            outStream.ToArray()
        else
            use inStream = new MemoryStream(bytes)
            use deflateStream = new DeflateStream(inStream, CompressionMode.Decompress)
            use outStream = new MemoryStream()
            deflateStream.CopyTo(outStream)
            outStream.ToArray()

    /// Compute a fast content hash from a list of (filename * filetext)
    let computeFilesFingerprint (files: (string * string) list) =
        use sha = SHA256.Create()
        use ms = new MemoryStream()
        use writer = new BinaryWriter(ms)
        let sortedFiles = files |> List.sortBy (fun (fn, _) -> Path.GetFileName fn)
        for fn, text in sortedFiles do
            writer.Write(Path.GetFileName fn)
            writer.Write(text.Length)
            let bytes = System.Text.Encoding.UTF8.GetBytes text
            writer.Write(bytes)
        writer.Flush()
        ms.Position <- 0L
        let hashBytes = sha.ComputeHash ms
        Convert.ToHexString(hashBytes).ToLowerInvariant()

    /// Compute a fast content hash from a single file's text
    let computeFileFingerprint (filename: string) (filetext: string) =
        use sha = SHA256.Create()
        let bytes = System.Text.Encoding.UTF8.GetBytes(filename + ":" + filetext)
        let hashBytes = sha.ComputeHash bytes
        Convert.ToHexString(hashBytes).ToLowerInvariant()

    let tryLoadRulesCache (cachePath: string) : CachedCwtRulesData option =
        try
            if File.Exists cachePath then
                let uncompressed = decompress cachePath
                Some(binarySerializer.UnPickle<CachedCwtRulesData> uncompressed)
            else
                None
        with _ ->
            None

    let saveRulesCache (cachePath: string) (data: CachedCwtRulesData) =
        try
            let pickled = binarySerializer.Pickle data
            compressAndWrite pickled cachePath
        with _ ->
            ()

    let tryLoadDocsCache (cachePath: string) : CachedDocsData option =
        try
            if File.Exists cachePath then
                let uncompressed = decompress cachePath
                Some(binarySerializer.UnPickle<CachedDocsData> uncompressed)
            else
                None
        with _ ->
            None

    let saveDocsCache (cachePath: string) (data: CachedDocsData) =
        try
            let pickled = binarySerializer.Pickle data
            compressAndWrite pickled cachePath
        with _ ->
            ()

    let tryLoadModifiersCache (cachePath: string) : CachedModifiersData option =
        try
            if File.Exists cachePath then
                let uncompressed = decompress cachePath
                Some(binarySerializer.UnPickle<CachedModifiersData> uncompressed)
            else
                None
        with _ ->
            None

    let saveModifiersCache (cachePath: string) (data: CachedModifiersData) =
        try
            let pickled = binarySerializer.Pickle data
            compressAndWrite pickled cachePath
        with _ ->
            ()
