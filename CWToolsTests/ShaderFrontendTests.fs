module ShaderFrontendTests

open System
open System.IO
open System.Collections.Concurrent
open System.Threading.Tasks
open Expecto
open CWTools.Games
open CWTools.Games.PdxShaderSyntax
open CWTools.Games.PdxShaderPreprocessor
open CWTools.Games.PdxShaderHlsl
open CWTools.Utilities.Position

[<Tests>]
let shaderSyntaxTests =
    testList
        "pdx shader lossless syntax"
        [ test "preserves every token and recovers declarations after damaged input" {
              let text =
                  "UnknownDialect Foo = { nested = { value = 1 } }\n"
                  + "Includes = { \"common.fxh\" nested = { \"not-direct.fxh\" } }\n"
                  + "Effect First { PixelShader = \"Pixel\" }\n"
                  + "VertexShader = { MainCode Vertex [[ float4 main( { return 0; } ]] }\n"
                  + "Effect Last { VertexShader = \"Vertex\" }\n"

              let tree = PdxShaderSyntax.parse "gfx/FX/test.shader" text
              Expect.isTrue tree.IsLossless "the token stream must cover the complete original UTF-16 text"

              let includes = PdxShaderSyntax.nodesOfKind ShaderNodeKind.IncludeFile tree |> List.map _.name
              Expect.equal includes [ Some "common.fxh" ] "only direct Includes entries are modeled as include nodes"

              let effects = PdxShaderSyntax.nodesOfKind ShaderNodeKind.Effect tree |> List.choose _.name
              Expect.equal effects [ "First"; "Last" ] "a damaged HLSL body must not hide later declarations"

              Expect.isNonEmpty
                  (PdxShaderSyntax.nodesOfKind ShaderNodeKind.Property tree)
                  "unknown dialect blocks are retained as lossless property nodes"
          }

          test "reports unterminated strings, comments, blocks and HLSL without throwing" {
              for text in [ "Effect A {"; "/* never closed"; "\"never closed"; "VertexShader = { MainCode A [[ float4 x;" ] do
                  let tree = PdxShaderSyntax.parse "broken.shader" text
                  Expect.isTrue tree.IsLossless "malformed input is still lossless"
                  Expect.isNonEmpty tree.diagnostics "malformed input has a recoverable syntax diagnostic"
          }

          test "deterministic malformed-input fuzz remains lossless" {
              let random = Random 739391
              let alphabet = "abcXYZ09_{}[]()=;:\"'/*#@!&| \r\n"

              for iteration in 0 .. 299 do
                  let length = random.Next(0, 600)
                  let chars = Array.init length (fun _ -> alphabet[random.Next alphabet.Length])
                  let text = String chars
                  let tree = PdxShaderSyntax.parse (sprintf "fuzz-%d.shader" iteration) text
                  Expect.isTrue tree.IsLossless (sprintf "fuzz input %d must be lossless" iteration)
          } ]

[<Tests>]
let shaderPreprocessorTests =
    testList
        "pdx shader variant preprocessor"
        [ test "records mutually exclusive branch presence conditions" {
              let text =
                  "#if defined(PDX_OPENGL) && !defined(PDX_DIRECTX_11)\nfloat OpenGlOnly;\n"
                  + "#elif PDX_PSSL\nfloat PsslOnly;\n#else\nfloat DirectXFallback;\n#endif\n"
                  + "@ifdef FEATURE_X\nfloat Feature;\n@endif\n"
              let tree = PdxShaderSyntax.parse "variants.fxh" text
              let result = PdxShaderPreprocessor.analyze tree
              let openGlCondition = conditionAt (text.IndexOf("OpenGlOnly", StringComparison.Ordinal)) result
              let psslCondition = conditionAt (text.IndexOf("PsslOnly", StringComparison.Ordinal)) result
              let fallbackCondition = conditionAt (text.IndexOf("DirectXFallback", StringComparison.Ordinal)) result

              let dx = defaultPlatformVariants |> List.find (fun variant -> variant.name = "directx11")
              let gl = defaultPlatformVariants |> List.find (fun variant -> variant.name = "opengl")
              let pssl = defaultPlatformVariants |> List.find (fun variant -> variant.name = "pssl")

              Expect.equal (evaluate gl.environment openGlCondition) ConditionTrue "OpenGL branch is active only for OpenGL"
              Expect.equal (evaluate dx.environment openGlCondition) ConditionFalse "DirectX does not activate OpenGL branch"
              Expect.equal (evaluate pssl.environment psslCondition) ConditionTrue "elif branch retains its own condition"
              Expect.equal (evaluate dx.environment fallbackCondition) ConditionTrue "else excludes all previous branches"
              Expect.isEmpty result.diagnostics "balanced directives are valid"
          }

          test "distinguishes object, function and bounded recursive macros" {
              let text = "#define VALUE 4\n#define ADD(X,Y) ((X)+(Y))\n#define A B\n#define B A\n"
              let tree = PdxShaderSyntax.parse "macros.fxh" text
              let result = PdxShaderPreprocessor.analyze tree
              let value = result.macros |> List.find (fun macro -> macro.name = "VALUE")
              let add = result.macros |> List.find (fun macro -> macro.name = "ADD")
              Expect.equal value.kind ObjectLike "object macros retain their kind"
              Expect.equal add.kind (FunctionLike [ "X"; "Y" ]) "function macro parameters are retained"

              let expanded =
                  expandObjectMacro
                      8
                      { defined = Set.empty
                        values = Map.empty }
                      result.macros
                      "A"

              Expect.isLessThanOrEqual expanded.expansionStack.Length 9 "recursive macros stop at the configured bound"
          } ]

[<Tests>]
let shaderHlslTests =
    testList
        "pdx shader HLSL binding"
        [ test "builds struct fields, overloads, locals, members and calls from raw fxh" {
              let text =
                  "struct Light { float3 Color; float Intensity; };\n"
                  + "float Shade(float value) { return value; }\n"
                  + "float3 Shade(float3 value) { return value; }\n"
                  + "float3 Apply(Light light) { float3 local = Shade(light.Color); return local * light.Intensity; }\n"
              let _, _, analysis = PdxShaderHlsl.analyzeText "lighting.fxh" text
              let structSymbol = analysis.symbols |> List.find (fun symbol -> symbol.kind = StructSymbol && symbol.name = "Light")
              let fields = analysis.symbols |> List.filter (fun symbol -> symbol.kind = FieldSymbol) |> List.map _.name
              let overloads = analysis.symbols |> List.filter (fun symbol -> symbol.kind = FunctionSymbol && symbol.name = "Shade")

              Expect.equal structSymbol.symbolType (StructType "Light") "struct declarations create a named type"
              Expect.containsAll fields [ "Color"; "Intensity" ] "struct members are available to binding"
              Expect.equal overloads.Length 2 "function overloads are not collapsed by name"
              Expect.exists analysis.symbols (fun symbol -> symbol.kind = LocalVariableSymbol && symbol.name = "local") "locals have lexical/function scope"
              Expect.exists analysis.references (fun reference -> reference.kind = MemberReference && reference.name = "Color") "member reads are classified"
              Expect.exists analysis.calls (fun call -> call.calleeIds |> List.exists (fun id -> id.Contains(":Shade:", StringComparison.Ordinal))) "call graph links function calls"

              let selected = resolveOverload [ VectorType(Float, 3) ] overloads
              Expect.equal selected.Length 1 "conversion scoring selects one overload"
              Expect.equal selected.Head.symbolType (VectorType(Float, 3)) "the vector overload wins"

              let vectorOverload = overloads |> List.find (fun symbol -> symbol.parameters.Head.parameterType = VectorType(Float, 3))
              let shadeCall = analysis.calls |> List.find (fun call -> call.span.startOffset = text.LastIndexOf("Shade", StringComparison.Ordinal))
              Expect.equal shadeCall.calleeIds [ vectorOverload.id ] "argument inference narrows the call edge to the selected overload"
          }

          test "member binding uses the receiver type and lexical shadowing uses the nearest scope" {
              let text =
                  "struct A { float FromA; };\n"
                  + "struct B { float FromA; };\n"
                  + "float Read(A item, float value) { { float value = item.FromA; value = value + 1.0; } return value; }\n"
              let _, _, analysis = PdxShaderHlsl.analyzeText "scopes.fxh" text
              let fields = analysis.symbols |> List.filter (fun symbol -> symbol.kind = FieldSymbol && symbol.name = "FromA")
              let memberReference = analysis.references |> List.find (fun reference -> reference.kind = MemberReference && reference.name = "FromA")
              Expect.equal memberReference.candidateIds.Length 1 "same-named fields on unrelated structs are not pooled"

              let aField =
                  fields
                  |> List.find (fun field -> memberReference.candidateIds |> List.contains field.id)
              let aStructScope = analysis.scopes |> List.find (fun scope -> scope.id = aField.scopeId)
              let aStruct =
                  analysis.symbols
                  |> List.find (fun symbol ->
                      symbol.kind = StructSymbol
                      && symbol.span.startOffset = aStructScope.span.startOffset)
              Expect.equal aStruct.name "A" "the receiver's declared struct selects its own field"

              let valueDeclarations =
                  analysis.symbols
                  |> List.filter (fun symbol ->
                      symbol.name = "value"
                      && (symbol.kind = ParameterSymbol || symbol.kind = LocalVariableSymbol))
              let parameter = valueDeclarations |> List.find (fun symbol -> symbol.kind = ParameterSymbol)
              let local = valueDeclarations |> List.find (fun symbol -> symbol.kind = LocalVariableSymbol)
              let valueReads =
                  analysis.references
                  |> List.filter (fun reference -> reference.name = "value" && reference.kind <> TypeReference)
                  |> List.sortBy _.span.startOffset
              Expect.exists valueReads (fun reference -> reference.candidateIds = [ local.id ]) "the nested block resolves to its local shadow"
              Expect.equal valueReads.Tail.Head.candidateIds [ local.id ] "both inner reads stay in the lexical scope"
              Expect.equal valueReads[valueReads.Length - 1].candidateIds [ parameter.id ] "the return after the block resolves to the parameter"
              Expect.exists analysis.scopes (fun scope -> scope.kind = LexicalScope) "nested braces materialize a lexical scope"
          }

          test "validates stage-only intrinsics in embedded MainCode" {
              let text =
                  "VertexShader = { MainCode Vertex [[ float4 main(float4 p) { return ddx(p); } ]] }\n"
                  + "PixelShader = { MainCode Pixel [[ float4 main(float4 p) : PDX_COLOR { return ddx(p); } ]] }\n"
              let _, _, analysis = PdxShaderHlsl.analyzeText "stages.shader" text
              let stageErrors = analysis.diagnostics |> List.filter (fun diagnostic -> diagnostic.code = "CWFX402")
              Expect.equal stageErrors.Length 1 "only the vertex invocation of ddx violates stage constraints"
              Expect.equal stageErrors.Head.stage VertexStage "the diagnostic retains stage provenance"
          } ]

let private positionAt (text: string) offset =
    let bounded = max 0 (min text.Length offset)
    let before = text.Substring(0, bounded)
    let line = 1 + (before |> Seq.filter ((=) '\n') |> Seq.length)
    let lastBreak = before.LastIndexOf('\n')
    let column = if lastBreak < 0 then bounded else bounded - lastBreak - 1
    mkPos line column

[<Tests>]
let shaderLanguageServiceContractTests =
    testList
        "pdx shader language-service contract"
        [ test "references, rename and user signature help share one HLSL binding" {
              let text =
                  "float4 Helper(float2 uv, float strength) { return float4(uv, strength, 1.0); }\n"
                  + "float4 Caller(float2 uv) { return Helper(uv, 0.5); }\n"
              let path = "C:/mod/gfx/FX/contracts.fxh"
              let helperCall = text.LastIndexOf("Helper", StringComparison.Ordinal)
              let references = PdxShaderFeatures.referencesAt [] (positionAt text helperCall) path text
              Expect.equal references.Length 2 "the declaration and call must bind to the same stable symbol"

              let rename = PdxShaderFeatures.renameTargetAt [] (positionAt text helperCall) path text
              Expect.isSome rename "a bound HLSL call is a rename target"
              Expect.equal rename.Value.name "Helper" "rename target name"
              Expect.equal rename.Value.edits.Length 2 "rename edits cover declaration and reference"

              let argumentEnd = text.LastIndexOf("0.5", StringComparison.Ordinal) + 3
              let signature = PdxShaderFeatures.signatureHelpAt [] (positionAt text argumentEnd) path text
              Expect.isSome signature "a user function call exposes signature help"
              Expect.equal signature.Value.activeParameter 1 "the comma selects the second parameter"
              Expect.stringContains signature.Value.signatures.Head.label "Helper" "signature label names the function"
          }

          test "built-in and constructor signature help is available without fabricated declarations" {
              let path = "C:/mod/gfx/FX/intrinsics.fxh"
              let builtinText = "float4 Main(float4 a, float4 b) { return lerp(a, b, 0.5); }\n"
              let builtinOffset = builtinText.IndexOf("0.5", StringComparison.Ordinal) + 3
              let builtin = PdxShaderFeatures.signatureHelpAt [] (positionAt builtinText builtinOffset) path builtinText
              Expect.isSome builtin "known HLSL intrinsics have profile signatures"
              Expect.equal builtin.Value.activeParameter 2 "intrinsic signature tracks the third parameter"

              let constructorText = "float4 Main(float2 uv) { return float4(uv, 0.0, 1.0); }\n"
              let constructorOffset = constructorText.IndexOf("1.0", StringComparison.Ordinal) + 3
              let constructor = PdxShaderFeatures.signatureHelpAt [] (positionAt constructorText constructorOffset) path constructorText
              Expect.isSome constructor "HLSL type constructors expose overloads"
              Expect.isGreaterThan constructor.Value.signatures.Length 1 "vector constructors retain overload choices"
          }

          test "semantic tokens include inactive DirectX branches and stable declaration modifiers" {
              let text = "#if PDX_OPENGL\nfloat GlOnly;\n#endif\nfloat Always;\n"
              let tokens = PdxShaderFeatures.semanticTokens "variants.fxh" text
              let tokenText (token: PdxShaderFeatures.ShaderSemanticToken) =
                  text.Substring(token.span.startOffset, token.span.Length)
              let gl = tokens |> List.find (tokenText >> (=) "GlOnly")
              let always = tokens |> List.find (tokenText >> (=) "Always")
              Expect.isTrue gl.declaration "global declarations are marked as declarations"
              Expect.isTrue gl.inactive "the OpenGL-only declaration is inactive in the default DirectX profile"
              Expect.isFalse always.inactive "unconditional code stays active"
          }

          test "formatter is idempotent, preserves HLSL bodies and selection/folding stay nested" {
              let text =
                  "VertexShader =\n{\nMainCode Vertex\n[[\n  float4 main() { return float4(1.0); }\n]]\n}\n"
                  + "Effect Example\n{\nVertexShader = \"Vertex\"\n}\n"
              let path = "C:/mod/gfx/FX/format.shader"
              let formatted = PdxShaderFeatures.formatDocument true 4 path text
              let formattedTwice = PdxShaderFeatures.formatDocument true 4 path formatted
              Expect.equal formattedTwice formatted "formatting must be idempotent"
              Expect.stringContains formatted "  float4 main()" "minimal formatting leaves embedded HLSL indentation untouched"

              let effectOffset = formatted.IndexOf("Example", StringComparison.Ordinal)
              let selections = PdxShaderFeatures.selectionRangesAt (positionAt formatted effectOffset) path formatted
              Expect.isGreaterThan selections.Length 1 "selection ranges grow from the Effect name to enclosing nodes"
              let folds = PdxShaderFeatures.foldingRanges path formatted
              Expect.isNonEmpty folds "multiline DSL and HLSL nodes expose folding ranges"
          }

          test "inlay hints expose inferred parameter and local types" {
              let text = "float4 Main(float2 uv) { float weight = 1.0; return float4(uv, weight, 1.0); }\n"
              let hints = PdxShaderFeatures.inlayHints "hints.fxh" text
              Expect.exists hints (fun hint -> hint.label = ": float2") "parameter type hint"
              Expect.exists hints (fun hint -> hint.label = ": float") "local type hint"
          } ]

let private shaderFixtureResources fixtureName =
    let root = Path.Combine(__SOURCE_DIRECTORY__, "testfiles", "shader-mods", fixtureName)
    Directory.GetFiles(root, "*", SearchOption.AllDirectories)
    |> Array.filter PdxShaderProject.isShaderFile
    |> Array.sort
    |> Array.map (fun filepath ->
        let relative = Path.GetRelativePath(root, filepath).Replace('\\', '/')
        let slash = relative.IndexOf('/')
        let scope = if slash < 0 then "mod" else relative.Substring(0, slash)
        let logicalPath = if slash < 0 then relative else relative.Substring(slash + 1)
        FileWithContentResource(
            filepath,
            { scope = scope
              filetext = File.ReadAllText filepath
              filepath = filepath
              logicalpath = logicalPath
              overwrite = Overwrite.No
              validate = true }
        ))
    |> Array.toList

[<Tests>]
let shaderModFixtureAndStressTests =
    testList
        "pdx shader real mod fixtures and stress"
        [ test "pure override fixture selects the mod copy and excludes vanilla-only symbols" {
              let resources = shaderFixtureResources "pure-override"
              let main = resources |> List.pick (function FileWithContentResource(_, resource) when resource.logicalpath.EndsWith("main.shader") -> Some resource | _ -> None)
              let unit, _ = PdxShaderRuntime.compileUnitFor resources [] main.filepath |> Option.get
              let declarations = unit.effective |> List.collect PdxShaderRuntime.declarationsFromSnapshot
              Expect.exists declarations (fun item -> item.name = "ModOnly") "mod override contributes symbols"
              Expect.isFalse (declarations |> List.exists (fun item -> item.name = "VanillaOnly")) "overridden vanilla copy is not effective"
              Expect.isEmpty (PdxShaderFeatures.validateFromResources resources main.filepath main.filetext) "fixture validates through its effective compile unit"
          }
          test "include extension fixture reaches vanilla through a mod include" {
              let resources = shaderFixtureResources "include-extension"
              let main = resources |> List.pick (function FileWithContentResource(_, resource) when resource.logicalpath.EndsWith("main.shader") -> Some resource | _ -> None)
              let unit, _ = PdxShaderRuntime.compileUnitFor resources [] main.filepath |> Option.get
              let logicalPaths = unit.effective |> List.map _.logicalPath
              Expect.containsAll logicalPaths [ "gfx/FX/main.shader"; "gfx/FX/extension.fxh"; "gfx/FX/base.fxh" ] "transitive vanilla extension graph"
              Expect.isEmpty unit.problems "extension graph resolves without ambiguity or cycles"
          }
          test "large graph rewrite fixture deduplicates its shared diamond dependency" {
              let resources = shaderFixtureResources "large-graph-rewrite"
              let main = resources |> List.pick (function FileWithContentResource(_, resource) when resource.logicalpath.EndsWith("root.shader") -> Some resource | _ -> None)
              let unit, _ = PdxShaderRuntime.compileUnitFor resources [] main.filepath |> Option.get
              Expect.equal unit.effective.Length 6 "root, two branches, common and two leaves are reachable exactly once"
              Expect.equal (unit.effective |> List.filter (fun snapshot -> snapshot.logicalPath.EndsWith("common.fxh")) |> List.length) 1 "diamond common include is deduplicated"
              Expect.isEmpty unit.problems "rewritten graph stays valid"
          }
          test "ten large mod graphs remain deterministic within a bounded performance budget" {
              let snapshots =
                  [ for modIndex in 0 .. 9 do
                        let prefix = sprintf "mods/m%d/gfx/FX" modIndex
                        let make name text = PdxShaderProject.createSnapshot PdxShaderProject.Workspace (sprintf "C:/%s/%s" prefix name) (sprintf "%s/%s" prefix name) text
                        yield make "root.shader" (sprintf "Includes = { \"%s/a.fxh\" \"%s/b.fxh\" }" prefix prefix)
                        yield make "a.fxh" (sprintf "Includes = { \"%s/common.fxh\" \"%s/la.fxh\" }" prefix prefix)
                        yield make "b.fxh" (sprintf "Includes = { \"%s/common.fxh\" \"%s/lb.fxh\" }" prefix prefix)
                        yield make "common.fxh" "float4 Common(float2 uv) { return float4(uv, 0.0, 1.0); }"
                        yield make "la.fxh" "float4 A(float2 uv) { return float4(uv.x, 0.0, 0.0, 1.0); }"
                        yield make "lb.fxh" "float4 B(float2 uv) { return float4(0.0, uv.y, 0.0, 1.0); }" ]
              let stopwatch = Diagnostics.Stopwatch.StartNew()
              let units = snapshots |> List.filter (fun snapshot -> snapshot.displayPath.EndsWith("root.shader")) |> List.map (PdxShaderProject.buildCompileUnit snapshots)
              for unit in units do
                  Expect.equal unit.effective.Length 6 "each graph has the expected bounded member count"
                  Expect.isEmpty unit.problems "each generated graph resolves"
              stopwatch.Stop()
              Expect.isLessThan stopwatch.ElapsedMilliseconds 15000L "10x graph analysis performance budget"
          }
          test "include depth budget returns a partial compile unit instead of recursing without bound" {
              let snapshots =
                  [ for index in 0 .. PdxShaderProject.maxIncludeDepth do
                        let logicalPath = sprintf "gfx/FX/depth-%d.fxh" index
                        let text =
                            if index = PdxShaderProject.maxIncludeDepth then
                                "float4 Leaf() { return float4(1.0); }"
                            else
                                sprintf "Includes = { \"gfx/FX/depth-%d.fxh\" }" (index + 1)

                        yield
                            PdxShaderProject.createSnapshot
                                PdxShaderProject.Workspace
                                (sprintf "C:/depth/%s" logicalPath)
                                logicalPath
                                text ]

              let unit = PdxShaderProject.buildCompileUnit snapshots snapshots.Head
              Expect.equal unit.members.Length PdxShaderProject.maxIncludeDepth "the depth limit is a hard member boundary"
              Expect.exists unit.problems (function
                  | PdxShaderProject.IncludeBudgetExceeded(_, _, _, _, "depth", limit) ->
                      limit = PdxShaderProject.maxIncludeDepth
                  | _ -> false) "depth exhaustion is structured and observable"
          }
          test "shadow copies cannot bypass the compile-unit member budget" {
              let root =
                  PdxShaderProject.createSnapshot
                      PdxShaderProject.Workspace
                      "C:/root/gfx/FX/root.shader"
                      "gfx/FX/root.shader"
                      "Includes = { \"gfx/FX/shared.fxh\" }"

              let copies =
                  [ for index in 0 .. PdxShaderProject.maxCompileUnitMembers + 16 do
                        yield
                            PdxShaderProject.createSnapshot
                                (PdxShaderProject.Dependency index)
                                (sprintf "C:/dependencies/%d/gfx/FX/shared.fxh" index)
                                "gfx/FX/shared.fxh"
                                (sprintf "float4 Copy%d() { return float4(1.0); }" index) ]

              let unit = PdxShaderProject.buildCompileUnit (root :: copies) root
              Expect.equal unit.members.Length PdxShaderProject.maxCompileUnitMembers "effective and overridden members share one hard cap"
              Expect.exists unit.problems (function
                  | PdxShaderProject.IncludeBudgetExceeded(_, _, _, _, "members", limit) ->
                      limit = PdxShaderProject.maxCompileUnitMembers
                  | _ -> false) "truncated definition candidates are reported"
          }
          test "semantic and include caches remain bounded across many document versions" {
              for index in 0 .. 699 do
                  let snapshot =
                      PdxShaderProject.createSnapshot
                          PdxShaderProject.CurrentDocument
                          (sprintf "C:/cache/version-%d.fxh" index)
                          (sprintf "gfx/FX/version-%d.fxh" index)
                          (sprintf "float4 Version%d() { return float4(1.0); }" index)

                  PdxShaderProject.semanticSnapshot snapshot |> ignore
                  PdxShaderProject.extractIncludes snapshot |> ignore

              let stats = PdxShaderProject.cacheStats ()
              Expect.isTrue (stats.semanticEntries > 0 && stats.semanticEntries <= stats.semanticLimit) "semantic LRU respects its cap"
              Expect.isTrue (stats.includeEntries > 0 && stats.includeEntries <= stats.includeLimit) "include LRU respects its cap"
          }
          test "concurrent same-path document versions never cross-contaminate semantic snapshots" {
              let failures = ConcurrentQueue<string>()
              Parallel.For(
                  0,
                  64,
                  fun index ->
                      let name = if index % 2 = 0 then "EvenVersion" else "OddVersion"
                      let text = sprintf "float4 %s() { return float4(1.0); }" name
                      let snapshot = PdxShaderProject.createSnapshot PdxShaderProject.CurrentDocument "C:/mod/gfx/FX/race.fxh" "gfx/FX/race.fxh" text
                      let semantic = PdxShaderProject.semanticSnapshot snapshot
                      if not (semantic.hlsl.symbols |> List.exists (fun symbol -> symbol.name = name)) then failures.Enqueue name)
              |> ignore
              Expect.isEmpty failures "content-hash cache keys isolate racing document versions"
          }
          test "generated valid documents keep declarations through idempotent parse-format-parse" {
              let random = Random 44821
              for index in 0 .. 99 do
                  let spaces = String(' ', random.Next(0, 9))
                  let text = sprintf "%sEffect E%d\n%s{\n%sPixelShader = \"P%d\"\n%s}\n" spaces index spaces spaces index spaces
                  let formatted = PdxShaderFeatures.formatDocument true 4 (sprintf "generated-%d.shader" index) text
                  let formattedTwice = PdxShaderFeatures.formatDocument true 4 (sprintf "generated-%d.shader" index) formatted
                  Expect.equal formattedTwice formatted "formatter property: idempotent"
                  let before = PdxShaderSyntax.parse "before.shader" text |> PdxShaderSyntax.nodesOfKind ShaderNodeKind.Effect |> List.choose _.name
                  let after = PdxShaderSyntax.parse "after.shader" formatted |> PdxShaderSyntax.nodesOfKind ShaderNodeKind.Effect |> List.choose _.name
                  Expect.equal after before "parse/format/parse preserves declarations"
          } ]
