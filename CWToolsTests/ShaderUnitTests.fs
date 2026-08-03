module ShaderUnitTests

open TestHelpers

open System
open System.IO
open System.Reflection
open CWTools.Common.STLConstants
open CWTools.Games
open CWTools.Games.Stellaris
open CWTools.Parser
open CWTools.Parser.CKPrinter
open CWTools.Parser.DocsParser
open CWTools.Utilities
open CWTools.Utilities.Position
open CWTools.Utilities.Utils
open CWTools
open CWTools.Validation
open Expecto
open Expecto.Logging
open Expecto.Logging.Message
open CWTools.Common
open CWTools.Process
open CWTools.Process.Localisation
open CWTools.Process.ProcessCore
open CWTools.Games.Files
open System.Threading
open System.Globalization
open System.Text
open FParsec
open LogCaptureTest
open MBrace.FsPickler



[<Tests>]
let pdxShaderFeatureTests =
    let shaderResource filepath filetext : Resource =
        FileWithContentResource(
            filepath,
            { scope = "mod"
              filetext = filetext
              filepath = filepath
              logicalpath = filepath
              overwrite = Overwrite.No
              validate = true }
        )

    let cursorAtMarker (text: string) =
        let marker = text.IndexOf('|')
        Expect.isGreaterThan marker -1 "test shader cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let label =
        function
        | CompletionResponse.Simple(label, _, _) -> label
        | CompletionResponse.Detailed(label, _, _, _) -> label
        | CompletionResponse.Snippet(label, _, _, _, _) -> label

    let sharedResource =
        shaderResource
            "gfx/FX/shared.fxh"
            """
VertexShader =
{
    MainCode VanillaVertex
    [[
        float4 main() { return float4(1.0f); }
    ]]
}

BlendState VanillaBlend
{
    BlendEnable = yes
}

PixelShader =
{
    MainCode PixelPdxMeshWhiteHole
    [[
        #ifdef WHITE_HOLE
        float4 main() { return float4(1.0f); }
        #endif
    ]]
}
"""

    testList
        "pdx shader features"
        [ test "complete vanilla cached shader symbols" {
              let text, cursor =
                  cursorAtMarker
                      """
Includes = { "shared.fxh" }

Effect Example
{
    VertexShader = "Van|"
}
"""

              let labels =
                  PdxShaderFeatures.completeFromResources [ sharedResource ] cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "VanillaVertex" "cached FX MainCodes should feed LSP completion"
          }
          test "complete DSL field types" {
              let text, cursor =
                  cursorAtMarker
                      """
VertexStruct VS_INPUT
{
    flo|
}
"""

              let labels =
                  PdxShaderFeatures.completeFromResources [] cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "float4" "vertex struct members should complete FX field types"
          }
          test "complete cached shader symbols directly after assignment" {
              let text, cursor =
                  cursorAtMarker
                      """
Includes = { "shared.fxh" }

Effect Example
{
    PixelShader = |
}
"""

              let labels =
                  PdxShaderFeatures.completeFromResources [ sharedResource ] cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "PixelPdxMeshWhiteHole" "FX references should complete before opening a quoted value"
          }
          test "complete Effect Defines from cached shader conditions" {
              let text, cursor =
                  cursorAtMarker
                      """
Includes = { "shared.fxh" }

Effect Example
{
    Defines = { "WH|" }
}
"""

              let labels =
                  PdxShaderFeatures.completeFromResources [ sharedResource ] cursor "gfx/FX/current.shader" text
                  |> List.map label

              Expect.contains labels "WHITE_HOLE" "Effect Defines should complete preprocessor condition names"

              let bareText, bareCursor =
                  cursorAtMarker
                      """
Includes = { "shared.fxh" }

Effect Example
{
    Defines = { | }
}
"""

              let bareLabels =
                  PdxShaderFeatures.completeFromResources [ sharedResource ] bareCursor "gfx/FX/current.shader" bareText
                  |> List.map label

              Expect.contains bareLabels "WHITE_HOLE" "Effect Defines should complete before opening a quoted value"
          }
          test "validate against cached FX symbols" {
              let text =
                  """
Includes = { "shared.fxh" }

Effect Example
{
    VertexShader = "VanillaVertex"
    PixelShader = "MissingPixel"
    BlendState = "VanillaBlend"
}
"""

              let errors =
                  PdxShaderFeatures.validateFromResources [ sharedResource ] "gfx/FX/current.shader" text

              Expect.exists
                  errors
                  (fun e -> e.code = "CWFX001" && e.message.Contains("MissingPixel"))
                  "missing FX references should still be diagnosed"

              Expect.isFalse
                  (errors |> List.exists (fun e -> e.message.Contains("VanillaVertex") || e.message.Contains("shared.fxh")))
                  "cached vanilla definitions and include files should satisfy FX validation"
          }
          test "validate MainCode references case-insensitively" {
              let text =
                  """
Includes = { "shared.fxh" }

Effect PdxMeshWhitehole
{
    PixelShader = "PixelPdxMeshWhitehole"
}
"""

              let errors =
                  PdxShaderFeatures.validateFromResources [ sharedResource ] "gfx/FX/current.shader" text

              Expect.isFalse
                  (errors |> List.exists (fun e -> e.message.Contains("PixelPdxMeshWhitehole")))
                  "Effect references should match MainCode names even when casing differs"
          }
          test "document symbols expose FX declarations" {
              let text =
                  """
VertexShader =
{
    MainCode ExampleVertex
    [[
        float4 main() { return float4(1.0f); }
    ]]
}

Effect ExampleEffect
{
    VertexShader = "ExampleVertex"
}
"""

              let symbols = PdxShaderFeatures.documentSymbols "gfx/FX/current.shader" text
              let shaderBlock = symbols |> List.find (fun symbol -> symbol.name = "VertexShader")

              Expect.exists symbols (fun symbol -> symbol.name = "ExampleEffect") "effects should appear in FX outline"
              Expect.exists shaderBlock.children (fun symbol -> symbol.name = "ExampleVertex") "MainCode should nest under the shader block"
          }
          test "goto definition resolves cached FX references" {
              let text, cursor =
                  cursorAtMarker
                      """
Includes = { "shared.fxh" }

Effect Example
{
    VertexShader = "Vanilla|Vertex"
}
"""

              let target =
                  PdxShaderFeatures.goToDefinitionFromResources [ sharedResource ] cursor "gfx/FX/current.shader" text

              Expect.isSome target "cached FX definitions should be available to goto definition"
              Expect.equal target.Value.FileName (Path.GetFullPath "gfx/FX/shared.fxh") "goto definition should target the cached source"
          } ]

[<Tests>]
let pdxShaderCompileUnitTests =
    let shaderResource scope filepath logicalpath filetext : Resource =
        FileWithContentResource(
            filepath,
            { scope = scope
              filetext = filetext
              filepath = filepath
              logicalpath = logicalpath
              overwrite = Overwrite.No
              validate = true }
        )

    let vertexShaderBlock name =
        sprintf
            "VertexShader =\n{\n    MainCode %s\n    [[\n        float4 main() { return float4(1.0f); }\n    ]]\n}\n"
            name

    let cursorAtMarker (text: string) =
        let marker = text.IndexOf('|')
        Expect.isGreaterThan marker -1 "test shader cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let label =
        function
        | CompletionResponse.Simple(label, _, _) -> label
        | CompletionResponse.Detailed(label, _, _, _) -> label
        | CompletionResponse.Snippet(label, _, _, _, _) -> label

    testList
        "pdx shader compile units"
        [ test "symbols from non-included files are always hidden" {
              let resources =
                  [ shaderResource "mod" "gfx/FX/other.fxh" "gfx/FX/other.fxh" (vertexShaderBlock "OtherVertex") ]

              let text =
                  "Effect Example\n{\n    VertexShader = \"OtherVertex\"\n}\n"

              let v2errors =
                  PdxShaderFeatures.validateFromResources resources "gfx/FX/current.shader" text

              Expect.exists
                  v2errors
                  (fun e -> e.code = "CWFX001" && e.message.Contains("OtherVertex"))
                  "V2 must not see symbols from files that are not included"

              let includedText =
                  "Includes = { \"other.fxh\" }\n\nEffect Example\n{\n    VertexShader = \"OtherVertex\"\n}\n"

              let includedErrors =
                  PdxShaderFeatures.validateFromResources resources "gfx/FX/current.shader" includedText

              Expect.isEmpty includedErrors "included files must contribute their symbols to the compile unit"

              let completionText, cursor =
                  cursorAtMarker "Effect Example\n{\n    VertexShader = \"Oth|\"\n}\n"

              let v2labels =
                  PdxShaderFeatures.completeFromResources resources cursor "gfx/FX/current.shader" completionText
                  |> List.map label

              Expect.isFalse
                  (List.contains "OtherVertex" v2labels)
                  "V2 completion must not leak symbols from non-included files"

          }
          test "mod wins over vanilla for the same logical path" {
              let vanillaText =
                  (vertexShaderBlock "SharedVertex") + (vertexShaderBlock "VanillaOnlyVertex")

              let resources =
                  [ shaderResource "vanilla" "C:/vanilla/gfx/FX/shared.fxh" "gfx/FX/shared.fxh" vanillaText
                    shaderResource "mod" "C:/mod/gfx/FX/shared.fxh" "gfx/FX/shared.fxh" (vertexShaderBlock "SharedVertex") ]

              let text, cursor =
                  cursorAtMarker
                      "Includes = { \"gfx/FX/shared.fxh\" }\n\nEffect Example\n{\n    VertexShader = \"Shared|Vertex\"\n}\n"

              let target =
                  PdxShaderFeatures.goToDefinitionFromResources resources cursor "C:/mod/gfx/FX/main.shader" text

              Expect.isSome target "compile-unit definitions should resolve included references"
              Expect.equal
                  target.Value.FileName
                  (Path.GetFullPath "C:/mod/gfx/FX/shared.fxh")
                  "the mod copy must win over vanilla for the same logical path"

              let overriddenText =
                  "Includes = { \"gfx/FX/shared.fxh\" }\n\nEffect Example\n{\n    VertexShader = \"VanillaOnlyVertex\"\n}\n"

              let overriddenErrors =
                  PdxShaderFeatures.validateFromResources resources "C:/mod/gfx/FX/main.shader" overriddenText

              Expect.exists
                  overriddenErrors
                  (fun e -> e.code = "CWFX001" && e.message.Contains("VanillaOnlyVertex"))
                  "symbols only present in the overridden vanilla copy must not be visible"
          }
          test "ambiguous basename include yields no link and CWFX004" {
              let resources =
                  [ shaderResource "mod" "gfx/FX/shared.fxh" "gfx/FX/shared.fxh" ""
                    shaderResource "mod" "common/FX/shared.fxh" "common/FX/shared.fxh" "" ]

              let text = "Includes = { \"shared.fxh\" }\n"

              let links =
                  PdxShaderFeatures.documentLinks resources "current.shader" text

              Expect.isEmpty links "an ambiguous include must not produce a document link"

              let errors =
                  PdxShaderFeatures.validateFromResources resources "current.shader" text

              Expect.exists
                  errors
                  (fun e -> e.code = "CWFX004" && e.message.Contains("ambiguous"))
                  "an ambiguous include must report CWFX004"
          }
          test "include cycle reports CWFX004 without hanging" {
              let resources =
                  [ shaderResource "mod" "a.fxh" "a.fxh" "Includes = { \"current.shader\" }\n" ]

              let text = "Includes = { \"a.fxh\" }\n"

              let errors =
                  PdxShaderFeatures.validateFromResources resources "current.shader" text

              Expect.exists
                  errors
                  (fun e -> e.code = "CWFX004" && e.message.Contains("cycle"))
                  "an include cycle must report CWFX004"
          }
          test "unsaved current-document text beats the on-disk copy" {
              let resources =
                  [ shaderResource "mod" "current.shader" "gfx/FX/current.shader" (vertexShaderBlock "DiskVertex") ]

              let text =
                  (vertexShaderBlock "UnsavedVertex")
                  + "Effect Example\n{\n    VertexShader = \"UnsavedVertex\"\n    VertexShader = \"DiskVertex\"\n}\n"

              let errors =
                  PdxShaderFeatures.validateFromResources resources "current.shader" text

              Expect.isFalse
                  (errors |> List.exists (fun e -> e.message.Contains("UnsavedVertex")))
                  "references satisfied by the unsaved text must not be diagnosed"

              Expect.exists
                  errors
                  (fun e -> e.code = "CWFX001" && e.message.Contains("DiskVertex"))
                  "the overridden on-disk copy must not contribute symbols"
          } ]

