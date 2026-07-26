module ShaderRuntimeTests

open System
open Expecto
open CWTools.Games
open CWTools.Games.PdxShaderRuntime

let private contentResource scope filepath logicalpath filetext : Resource =
    FileWithContentResource(
        filepath,
        { scope = scope
          filetext = filetext
          filepath = filepath
          logicalpath = logicalpath
          overwrite = Overwrite.No
          validate = true }
    )

let private shaderResource filepath logicalpath filetext =
    contentResource "mod" filepath logicalpath filetext

let private gfxResource filepath logicalpath filetext =
    contentResource "mod" filepath logicalpath filetext

let private effectText name = sprintf "Effect %s\n{\n}\n" name

// The ABI catalog is module-level state and Expecto runs test lists in parallel;
// every test that loads/resets a catalog must hold this lock for its whole body.
let private catalogTestLock = obj ()

[<Tests>]
let shaderLoadOrderOriginTests =
    testList
        "pdx shader explicit load order"
        [ test "workspace, ordered dependencies, vanilla and unknown roots stay distinct" {
              let roots: PdxShaderProject.ShaderLoadOrderRoot list =
                  [ { name = "primary"
                      path = PdxShaderProject.canonicalizePath "C:/mods/primary"
                      origin = PdxShaderProject.Workspace }
                    { name = "library-a"
                      path = PdxShaderProject.canonicalizePath "C:/mods/library-a"
                      origin = PdxShaderProject.Dependency 0 }
                    { name = "library-b"
                      path = PdxShaderProject.canonicalizePath "C:/mods/library-b"
                      origin = PdxShaderProject.Dependency 1 } ]
              let resolve scope path = PdxShaderProject.originForResourceWithRoots roots scope path
              Expect.equal (resolve "primary" "C:/mods/primary/gfx/FX/a.shader") PdxShaderProject.Workspace "primary root"
              Expect.equal (resolve "library-a" "C:/mods/library-a/gfx/FX/a.shader") (PdxShaderProject.Dependency 0) "first dependency"
              Expect.equal (resolve "library-b" "C:/mods/library-b/gfx/FX/a.shader") (PdxShaderProject.Dependency 1) "second dependency"
              Expect.equal (resolve "vanilla" "D:/Stellaris/gfx/FX/a.shader") PdxShaderProject.Vanilla "vanilla scope is authoritative"
              Expect.equal (resolve "unconfigured" "C:/loose/gfx/FX/a.shader") PdxShaderProject.Workspace "unknown root is conservative"
          } ]

let private buildWithCatalog gameVersion (catalogText: string) resources =
    lock catalogTestLock (fun () ->
        let catalogText =
            if catalogText.Contains("\"_schema\"", StringComparison.Ordinal) then catalogText
            else
                catalogText.Replace(
                    "{ \"entries\"",
                    "{ \"_schema\": \"cwtools/shader-abi-catalog/v1\", \"game\": \"stellaris\", \"entries\"",
                    StringComparison.Ordinal
                )
        loadShaderAbiCatalogFromText gameVersion "test-catalog" catalogText

        try
            buildModel gameVersion resources []
        finally
            resetShaderAbiCatalog ())

let private buildWithRendererContracts gameVersion contractText resources =
    lock catalogTestLock (fun () ->
        loadSpriteRendererContractsFromText gameVersion "test-renderer-contracts" contractText

        try
            buildModel gameVersion resources []
        finally
            resetSpriteRendererContracts ())

let private auditText version shaderFiles effectDeclarations uniqueEffectNames automaticPromotion confirmedEntries =
    sprintf
        """{
          "_schema": "cwtools/shader-abi-audit/v1",
          "game": "stellaris",
          "game_version": "%s",
          "review_status": "complete",
          "automatic_promotion": %s,
          "candidate_universe": {
            "shader_files": %d,
            "effect_declarations": %d,
            "unique_effect_names": %d,
            "inventory_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
          },
          "confirmed_engine_entries": [%s],
          "evidence_reviews": [
            { "stage": "vanilla_shader_inventory", "status": "reviewed" },
            { "stage": "textual_call_sites", "status": "reviewed" },
            { "stage": "renderer_contracts", "status": "reviewed" },
            { "stage": "executable_or_runtime", "status": "no_qualifying_evidence" }
          ]
        }"""
        version
        (if automaticPromotion then "true" else "false")
        shaderFiles
        effectDeclarations
        uniqueEffectNames
        confirmedEntries

[<Tests>]
let shaderRuntimeEvidenceTests =
    testList
        "pdx shader runtime evidence"
        [ test "shader = X in a .gfx source yields DataExplicit with an accurate span" {
              let gfxText =
                  "spriteType = {\n\tname = \"GFX_test\"\n\tshader = Foo\n}\n"

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/test.shader" "gfx/FX/test.shader" (effectText "Foo")
                    gfxResource "C:/mod/interface/test.gfx" "interface/test.gfx" gfxText ]

              let model = buildModel (Some "4.4.6") resources []
              let result = effectReachability model "Foo"

              Expect.isSome result "Foo must be a known declared effect"

              match result.Value.reachability with
              | DataExplicit evidence -> Expect.isNonEmpty evidence "data_explicit must carry its evidence"
              | other -> failtestf "expected DataExplicit, got %A" other

              Expect.equal result.Value.evidence.Length 1 "exactly one call site expected"
              let call = result.Value.evidence.Head
              Expect.equal call.kind ShaderAssignment "evidence kind"
              Expect.equal call.value "Foo" "evidence value is the effect name as written"
              Expect.equal call.sourceFile "C:/mod/interface/test.gfx" "evidence file"
              Expect.equal call.enclosingBlock (Some "spriteType") "enclosing block key"
              Expect.equal (int call.span.StartLine) 3 "span line of the shader value"
              Expect.equal (int call.span.StartColumn) 10 "span column of the shader value"
              Expect.equal (int call.span.EndColumn) 13 "span end column of the shader value"

              let callers = callersOf model "Foo"
              Expect.equal callers.Length 1 "callersOf must return the same located call site"
          }
          test "effectFile selects declaring file: candidate vs engine_or_unreferenced" {
              let gfxText =
                  "progressbartype = {\n\tname = \"GFX_progress\"\n\teffectFile = \"gfx/FX/buttonstate.shader\"\n}\n"

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/buttonstate.shader" "gfx/FX/buttonstate.shader" (effectText "Up")
                    shaderResource "C:/mod/gfx/FX/other.shader" "gfx/FX/other.shader" (effectText "Other")
                    gfxResource "C:/mod/interface/progress.gfx" "interface/progress.gfx" gfxText ]

              let model = buildModel (Some "4.4.6") resources []

              let up = effectReachability model "Up" |> Option.get

              match up.reachability with
              | EffectFileConventionCandidate evidence ->
                  Expect.equal evidence.Length 1 "the effectFile selection is the evidence"
                  Expect.equal evidence.Head.kind EffectFileSelection "evidence kind"
                  Expect.equal evidence.Head.enclosingBlock (Some "progressbartype") "enclosing block key"
              | other -> failtestf "expected EffectFileConventionCandidate, got %A" other

              let callers = callersOf model "Up"
              Expect.equal callers.Length 1 "effectFile evidence must be returned by the callers query"
              Expect.equal callers.Head.kind EffectFileSelection "callers includes the file-selection evidence"
              Expect.equal callers.Head.interfaceSprite (Some "GFX_progress") "evidence identifies the selecting sprite"
              Expect.equal callers.Head.rendererSubtype (Some "progress_bar") "evidence preserves the renderer subtype"

              let otherEffect = effectReachability model "Other" |> Option.get
              Expect.equal otherEffect.reachability EngineOrUnreferenced "effects in unselected files stay engine_or_unreferenced"
          }
          test "interface sprite invocation records direct inputs and static GUI uses" {
              let gfxText =
                  "spriteTypes = {\n\tframeAnimatedSpriteType = {\n\t\tname = \"GFX_animated_button\"\n\t\ttextureFile = \"gfx/interface/button.dds\"\n\t\teffectFile = \"gfx/FX/buttonstate.shader\"\n\t\tnoOfFrames = 4\n\t\tanimation = { animationmaskfile = \"gfx/interface/nested-mask.dds\" }\n\t}\n}\n"

              let guiText =
                  "containerWindowType = {\n\ticonType = {\n\t\tname = \"button_icon\"\n\t\tspriteType = \"GFX_animated_button\"\n\t}\n}\n"

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/buttonstate.shader" "gfx/FX/buttonstate.shader" (effectText "Up")
                    gfxResource "C:/mod/interface/button.gfx" "interface/button.gfx" gfxText
                    contentResource "mod" "C:/mod/interface/button.gui" "interface/button.gui" guiText ]

              let model = buildModel (Some "4.4.6") resources []
              Expect.equal model.interfaceSprites.Length 1 "one effectFile-bearing sprite is modeled"
              let invocation = model.interfaceSprites.Head
              Expect.equal invocation.spriteName (Some "GFX_animated_button") "sprite identity"
              Expect.equal invocation.rendererType "frameAnimatedSpriteType" "original renderer type"
              Expect.equal invocation.rendererSubtype "framed_animated_sprite" "stable renderer subtype"
              Expect.equal invocation.frameCount (Some 4) "frame contract input"
              Expect.equal
                  (invocation.resourceInputs |> List.map (fun input -> input.field, input.value))
                  [ "textureFile", "gfx/interface/button.dds" ]
                  "only direct renderer inputs are attached; nested animation fields stay separate"

              Expect.equal model.guiSpriteUses.Length 1 "one static .gui use is modeled"
              let guiUse = model.guiSpriteUses.Head
              Expect.equal guiUse.spriteName "GFX_animated_button" "GUI edge target"
              Expect.equal guiUse.enclosingBlock (Some "iconType") "GUI widget context"
          }
          test "non-gfx open documents cannot fabricate shader callers" {
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/test.shader" "gfx/FX/test.shader" (effectText "Foo") ]

              let model =
                  buildModel
                      (Some "4.4.6")
                      resources
                      [ "C:/mod/common/scripted_effects/test.txt", "some_effect = { shader = Foo }" ]

              Expect.equal model.evidence [] "only .gfx/.asset files are caller-evidence sources"
              Expect.equal
                  (effectReachability model "Foo" |> Option.get).reachability
                  EngineOrUnreferenced
                  "an unrelated open script must not make the Effect data-explicit"
          }
          test "runtime caches refresh provenance when resource metadata changes without a text edit" {
              let shaderPath = "C:/shared/gfx/FX/test.shader"
              let gfxPath = "C:/shared/interface/test.gfx"
              let shaderText = effectText "Foo"
              let gfxText = "spriteType = { name = \"GFX_test\" shader = Foo }"

              let vanillaModel =
                  buildModel
                      (Some "4.4.6")
                      [ contentResource "vanilla" shaderPath "gfx/FX/test.shader" shaderText
                        contentResource "vanilla" gfxPath "interface/test.gfx" gfxText ]
                      []

              Expect.equal vanillaModel.declarations.Head.origin PdxShaderProject.Vanilla "initial declaration provenance"
              Expect.equal vanillaModel.evidence.Head.origin PdxShaderProject.Vanilla "initial evidence provenance"

              let workspaceModel =
                  buildModel
                      (Some "4.4.6")
                      [ contentResource "mod" shaderPath "modded/FX/test.shader" shaderText
                        contentResource "mod" gfxPath "modded/interface/test.gfx" gfxText ]
                      []

              Expect.equal workspaceModel.declarations.Head.origin PdxShaderProject.Workspace "declaration cache key includes origin"
              Expect.equal workspaceModel.declarations.Head.logicalPath "modded/FX/test.shader" "declaration cache key includes logical path"
              Expect.equal workspaceModel.evidence.Head.origin PdxShaderProject.Workspace "evidence cache key includes origin"
              Expect.equal workspaceModel.evidence.Head.logicalPath "modded/interface/test.gfx" "evidence cache key includes logical path"
          }
          test "ambiguous effectFile suffix does not fabricate candidate reachability" {
              let gfxText =
                  "spriteType = {\n\teffectFile = \"shared.shader\"\n}\n"

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/shared.shader" "gfx/FX/shared.shader" (effectText "First")
                    shaderResource "C:/mod/other/FX/shared.shader" "other/FX/shared.shader" (effectText "Second")
                    gfxResource "C:/mod/interface/ambiguous.gfx" "interface/ambiguous.gfx" gfxText ]

              let model = buildModel (Some "4.4.6") resources []
              Expect.equal
                  (effectReachability model "First" |> Option.get).reachability
                  EngineOrUnreferenced
                  "ambiguous basename must not select the first file"
              Expect.equal
                  (effectReachability model "Second" |> Option.get).reachability
                  EngineOrUnreferenced
                  "ambiguous basename must not select either file"
          }
          test "comments and string contents never produce evidence" {
              let gfxText =
                  "spriteType = {\n\tname = \"GFX_\\\"shader = EscapedString\"\n\t// shader = Commented\n\t/* shader = Blocked */\n\t# shader = Hashed\n\ttext = \"shader = InsideString\"\n\tshader = Real\n}\n"

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/real.shader" "gfx/FX/real.shader" (effectText "Real")
                    gfxResource "C:/mod/interface/comments.gfx" "interface/comments.gfx" gfxText ]

              let model = buildModel (Some "4.4.6") resources []
              let values = model.evidence |> List.map (fun evidence -> evidence.value)
              Expect.equal values [ "Real" ] "only the genuine shader assignment may be recorded"
          }
          test "the DSL scanner rejects longer keys, complex values and unterminated strings" {
              let gfxText =
                  "spriteType = {\n\tmeshshader = WrongKey\n\tshader = Wrong/Path\n\tshader = { scripted = WrongClause }\n\teffectFile = gfx/FX/unquoted.shader\n\teffectFile = \"unterminated.shader\n}\n"

              let evidence =
                  extractEvidenceFromText
                      PdxShaderProject.Workspace
                      "C:/mod/interface/malformed.gfx"
                      "interface/malformed.gfx"
                      gfxText

              Expect.isEmpty evidence "malformed or non-scalar assignments must fail closed"
          } ]

[<Tests>]
let shaderRuntimeAbiCatalogTests =
    testList
        "pdx shader runtime ABI catalog"
        [ test "matching catalog entry classifies engine_hardcoded; mismatched version is stale" {
              let catalogText =
                  """{ "entries": [
                        { "game": "stellaris", "game_version": "4.4.6", "entry_kind": "effect", "name": "EngineEffect", "evidence": "manual_runtime_test", "rename_policy": "forbidden" },
                        { "game": "stellaris", "game_version": "3.0.0", "entry_kind": "effect", "name": "StaleEffect", "evidence": "executable_observation", "rename_policy": "forbidden" }
                     ] }"""

              let resources =
                  [ shaderResource
                        "C:/mod/gfx/FX/engine.shader"
                        "gfx/FX/engine.shader"
                        ((effectText "EngineEffect") + (effectText "StaleEffect")) ]

              let model = buildWithCatalog (Some "4.4.6") catalogText resources

              let engine = effectReachability model "EngineEffect" |> Option.get

              match engine.reachability with
              | EngineHardcoded entry ->
                  Expect.equal entry.name "EngineEffect" "catalog entry name"
                  Expect.equal entry.evidence ManualRuntimeTest "catalog evidence kind"
                  Expect.isFalse entry.stale "matching version entry is active"
              | other -> failtestf "expected EngineHardcoded, got %A" other

              let stale = effectReachability model "StaleEffect" |> Option.get
              Expect.equal stale.reachability EngineOrUnreferenced "version-mismatched entries must not classify"
              Expect.equal model.staleCatalogCount 1 "one stale entry is reported"
          }
          test "unknown analysis version makes every ABI catalog entry stale" {
              let catalogText =
                  """{ "entries": [
                        { "game": "stellaris", "game_version": "4.4.6", "entry_kind": "effect", "name": "EngineEffect", "evidence": "manual_runtime_test", "rename_policy": "forbidden" }
                     ] }"""

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/engine.shader" "gfx/FX/engine.shader" (effectText "EngineEffect") ]

              let model = buildWithCatalog None catalogText resources
              Expect.equal
                  (effectReachability model "EngineEffect" |> Option.get).reachability
                  EngineOrUnreferenced
                  "a catalog cannot prove an ABI when the running game version is unknown"
              Expect.equal model.staleCatalogCount 1 "the version-bound entry is reported as stale"
          }
          test "catalog schema and reviewed evidence fail closed with actionable diagnostics" {
              let invalid =
                  """{ "_schema": "wrong", "game": "stellaris", "entries": [
                        { "game": "stellaris", "game_version": "4.4.6", "entry_kind": "effect", "name": "Unsafe", "evidence": "guessed_from_no_callers", "rename_policy": "maybe" }
                     ] }"""
              let entries, diagnostics = validateShaderAbiCatalogText (Some "4.4.6") "invalid-test" invalid
              Expect.isEmpty entries "an invalid root schema cannot load trusted ABI entries"
              Expect.exists diagnostics (fun item -> item.code = "CWFXABI001") "schema error"
              Expect.exists diagnostics (fun item -> item.code = "CWFXABI109") "unreviewed evidence error"
              Expect.exists diagnostics (fun item -> item.code = "CWFXABI110") "rename policy error"
          }
          test "candidate report preserves unknown versus file-convention evidence" {
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/selected.shader" "gfx/FX/selected.shader" (effectText "SelectedCandidate")
                    shaderResource "C:/mod/gfx/FX/unknown.shader" "gfx/FX/unknown.shader" (effectText "UnknownCandidate")
                    gfxResource "C:/mod/interface/a.gfx" "interface/a.gfx" "spriteType = { effectFile = \"gfx/FX/selected.shader\" }" ]
              let report = buildModel (Some "4.4.6") resources [] |> abiCandidateReport
              let selected = report |> List.find (fun item -> item.name = "SelectedCandidate")
              let unknown = report |> List.find (fun item -> item.name = "UnknownCandidate")
              Expect.equal selected.classification "effect_file_convention_candidate" "file selection remains a renderer candidate"
              Expect.equal unknown.classification "engine_or_unreferenced" "no caller remains unknown"
              Expect.stringContains unknown.reviewReason "not proof" "the report forbids no-text-reference ABI promotion"
          }
          test "completed ABI audit verifies the vanilla candidate universe without promoting entries" {
              lock catalogTestLock (fun () ->
                  resetShaderAbiCatalog ()
                  loadShaderAbiAuditFromText (Some "4.4.6") "test-audit" (auditText "4.4.6" 2 3 2 false "")
                  try
                      let resources =
                          [ contentResource "vanilla" "C:/vanilla/gfx/FX/a.shader" "gfx/FX/a.shader" ((effectText "Alpha") + (effectText "Beta"))
                            contentResource "vanilla" "C:/vanilla/gfx/FX/b.shader" "gfx/FX/b.shader" (effectText "Alpha") ]
                      let verification = buildModel (Some "4.4.6") resources [] |> verifyShaderAbiAudit
                      Expect.equal verification.status "current" "matching reviewed inventory is current"
                      Expect.isTrue verification.corpusMatches "candidate counts match the vanilla model"
                      Expect.equal verification.confirmedEngineEntryCount 0 "an empty reviewed catalog stays empty"
                      Expect.isFalse verification.automaticPromotion "the audit cannot promote Effects"
                  finally
                      resetShaderAbiAudit ())
          }
          test "ABI audit rejects automatic promotion and fails closed on catalog mismatch" {
              let unsafeAudit = auditText "4.4.6" 1 1 1 true ""
              let parsed, diagnostics = validateShaderAbiAuditText (Some "4.4.6") "unsafe-audit" unsafeAudit
              Expect.isNone parsed "automatic promotion invalidates the audit"
              Expect.exists diagnostics (fun item -> item.code = "CWFXABIA006") "promotion policy diagnostic"

              lock catalogTestLock (fun () ->
                  resetShaderAbiCatalog ()
                  loadShaderAbiAuditFromText
                      (Some "4.4.6")
                      "mismatched-audit"
                      (auditText "4.4.6" 1 1 1 false "\"engineeffect|gfx/FX/engine.shader\"")
                  try
                      let resources =
                          [ contentResource "vanilla" "C:/vanilla/gfx/FX/engine.shader" "gfx/FX/engine.shader" (effectText "EngineEffect") ]
                      let verification = buildModel (Some "4.4.6") resources [] |> verifyShaderAbiAudit
                      Expect.equal verification.status "catalog_mismatch" "audit claims cannot bypass the curated catalog"
                  finally
                      resetShaderAbiAudit ())
          }
          test "version-mismatched ABI audit is stale" {
              lock catalogTestLock (fun () ->
                  loadShaderAbiAuditFromText (Some "4.4.7") "stale-audit" (auditText "4.4.6" 1 1 1 false "")
                  try
                      let resources =
                          [ contentResource "vanilla" "C:/vanilla/gfx/FX/a.shader" "gfx/FX/a.shader" (effectText "Alpha") ]
                      let verification = buildModel (Some "4.4.7") resources [] |> verifyShaderAbiAudit
                      Expect.equal verification.status "stale" "audit version mismatch is reported before corpus counts"
                  finally
                      resetShaderAbiAudit ())
          }
          test "4.4.6 to 4.4.7 ABI upgrade audit reports added removed retained and changed entries" {
              let catalog version entries =
                  sprintf "{ \"_schema\": \"cwtools/shader-abi-catalog/v1\", \"game\": \"stellaris\", \"game_version\": \"%s\", \"entries\": [%s] }" version entries
              let entry version name evidence policy =
                  sprintf "{ \"game\": \"stellaris\", \"game_version\": \"%s\", \"entry_kind\": \"effect\", \"name\": \"%s\", \"evidence\": \"%s\", \"rename_policy\": \"%s\" }" version name evidence policy
              let oldText =
                  catalog "4.4.6" (String.concat "," [ entry "4.4.6" "Retained" "manual_runtime_test" "forbidden"; entry "4.4.6" "Removed" "executable_observation" "forbidden"; entry "4.4.6" "Changed" "manual_runtime_test" "forbidden" ])
              let newText =
                  catalog "4.4.7" (String.concat "," [ entry "4.4.7" "Retained" "manual_runtime_test" "forbidden"; entry "4.4.7" "Added" "official_vanilla_contract" "forbidden"; entry "4.4.7" "Changed" "executable_observation" "allowed" ])
              let audit = auditShaderAbiCatalogUpgrade "4.4.6" oldText "4.4.7" newText
              Expect.equal audit.added [ "Added" ] "added ABI"
              Expect.equal audit.removed [ "Removed" ] "removed ABI"
              Expect.containsAll audit.retained [ "Changed"; "Retained" ] "retained identities"
              Expect.equal audit.changed [ "Changed" ] "review evidence/policy change"
              Expect.isEmpty audit.diagnostics "both version snapshots satisfy the schema"
          }
          test "versioned renderer contract confirms only listed Effects and validates inputs" {
              let contractText =
                  """{ "contracts": [
                        { "game": "stellaris", "game_version": "4.4.6", "renderer_subtype": "progress_bar", "shader_file": "gfx/FX/progress.shader", "effects": ["Color", "Texture"], "required_inputs": ["textureFile1", "textureFile2"], "evidence": "official_vanilla_contract" }
                     ] }"""
              let shaderText = effectText "Color" + effectText "Texture" + effectText "UnknownEntry"
              let gfxText =
                  "progressbartype = {\n\tname = \"GFX_progress\"\n\ttextureFile1 = \"empty.dds\"\n\ttextureFile2 = \"fill.dds\"\n\teffectFile = \"gfx/FX/progress.shader\"\n}\n"
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/progress.shader" "gfx/FX/progress.shader" shaderText
                    gfxResource "C:/mod/interface/progress.gfx" "interface/progress.gfx" gfxText ]

              let model = buildWithRendererContracts (Some "4.4.6") contractText resources

              for effectName in [ "Color"; "Texture" ] do
                  match (effectReachability model effectName |> Option.get).reachability with
                  | EffectFileConvention evidence -> Expect.equal evidence.Length 1 "contract reachability carries effectFile evidence"
                  | other -> failtestf "expected EffectFileConvention for %s, got %A" effectName other

              match (effectReachability model "UnknownEntry" |> Option.get).reachability with
              | EffectFileConventionCandidate _ -> ()
              | other -> failtestf "unlisted file member must remain a candidate, got %A" other

              Expect.equal
                  (validateRendererInvocation model model.interfaceSprites.Head)
                  []
                  "all required inputs and Effects satisfy the active contract"
          }
          test "renderer contracts are stale on a game-version mismatch" {
              let contractText =
                  """{ "contracts": [
                        { "game": "stellaris", "game_version": "4.4.5", "renderer_subtype": "progress_bar", "shader_file": "gfx/FX/progress.shader", "effects": ["Color"], "required_inputs": [] }
                     ] }"""
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/progress.shader" "gfx/FX/progress.shader" (effectText "Color")
                    gfxResource "C:/mod/interface/progress.gfx" "interface/progress.gfx" "progressbartype = { effectFile = \"gfx/FX/progress.shader\" }" ]
              let model = buildWithRendererContracts (Some "4.4.6") contractText resources

              match (effectReachability model "Color" |> Option.get).reachability with
              | EffectFileConventionCandidate _ -> ()
              | other -> failtestf "stale contract must not confirm reachability, got %A" other
          }
          test "empty catalog is the default and classifies nothing" {
              lock catalogTestLock (fun () ->
                  let resources =
                      [ shaderResource "C:/mod/gfx/FX/engine.shader" "gfx/FX/engine.shader" (effectText "EngineEffect") ]

                  resetShaderAbiCatalog ()
                  let model = buildModel (Some "4.4.6") resources []
                  let engine = effectReachability model "EngineEffect" |> Option.get
                  Expect.equal engine.reachability EngineOrUnreferenced "no textual reference alone is never engine_hardcoded")
          } ]

[<Tests>]
let shaderRuntimeRenamePolicyTests =
    testList
        "pdx shader runtime rename policy"
        [ test "rename policy matrix covers all five classifications" {
              let catalogText =
                  """{ "entries": [
                        { "game": "stellaris", "game_version": "4.4.6", "entry_kind": "effect", "name": "HardcodedEffect", "evidence": "manual_runtime_test", "rename_policy": "forbidden" },
                        { "game": "stellaris", "game_version": "4.4.6", "entry_kind": "effect", "name": "HardcodedAllowedEffect", "evidence": "official_vanilla_contract", "rename_policy": "allowed" }
                     ] }"""

              let selectedText = (effectText "CandidateEffect")
              let mainText = (effectText "ExplicitEffect") + (effectText "LonelyEffect")
              let engineText = (effectText "HardcodedEffect") + (effectText "HardcodedAllowedEffect")

              let gfxText =
                  "spriteType = {\n\tname = \"GFX_a\"\n\tshader = ExplicitEffect\n\teffectFile = \"gfx/FX/selected.shader\"\n}\n"

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/main.shader" "gfx/FX/main.shader" mainText
                    shaderResource "C:/mod/gfx/FX/selected.shader" "gfx/FX/selected.shader" selectedText
                    shaderResource "C:/mod/gfx/FX/engine.shader" "gfx/FX/engine.shader" engineText
                    gfxResource "C:/mod/interface/a.gfx" "interface/a.gfx" gfxText ]

              let model = buildWithCatalog (Some "4.4.6") catalogText resources

              let decision name = renamePolicy model name

              match decision "ExplicitEffect" with
              | RenameAllowed _ -> ()
              | other -> failtestf "data_explicit rename must be allowed (preview), got %A" other

              match decision "CandidateEffect" with
              | RenameDenied reason ->
                  Expect.stringContains reason "convention" "candidate denial must explain the convention risk"
              | other -> failtestf "effect_file_convention_candidate rename must be denied, got %A" other

              match renamePolicyForReachability (EffectFileConvention []) with
              | RenameDenied _ -> ()
              | other -> failtestf "effect_file_convention rename must be denied, got %A" other

              match decision "HardcodedEffect" with
              | RenameDenied _ -> ()
              | other -> failtestf "forbidden ABI entry rename must be denied, got %A" other

              match decision "HardcodedAllowedEffect" with
              | RenameAllowed _ -> ()
              | other -> failtestf "catalog-allowed ABI entry rename must be allowed, got %A" other

              match decision "LonelyEffect" with
              | RenameRequiresExplicitForce _ -> ()
              | other -> failtestf "engine_or_unreferenced rename must require explicit force, got %A" other

              match decision "NotDeclared" with
              | RenameDenied _ -> ()
              | other -> failtestf "undeclared names must be denied, got %A" other
          }
          test "duplicate Effect names require explicit force even with a direct caller" {
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/a.shader" "gfx/FX/a.shader" (effectText "Shared")
                    shaderResource "C:/mod/gfx/FX/b.shader" "gfx/FX/b.shader" (effectText "Shared")
                    gfxResource "C:/mod/interface/a.gfx" "interface/a.gfx" "spriteType = { shader = Shared }" ]

              let model = buildModel (Some "4.4.6") resources []

              match renamePolicy model "Shared" with
              | RenameRequiresExplicitForce reason ->
                  Expect.stringContains reason "2 declarations" "the decision explains the ambiguous declarations"
              | other -> failtestf "a name-only rename across duplicate Effects is unsafe, got %A" other
          }
          test "a direct caller does not make rename safe when effectFile also selects the declaring file" {
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/mixed.shader" "gfx/FX/mixed.shader" (effectText "Mixed")
                    gfxResource
                        "C:/mod/interface/mixed.gfx"
                        "interface/mixed.gfx"
                        "spriteType = { name = \"GFX_mixed\" shader = Mixed effectFile = \"gfx/FX/mixed.shader\" }" ]

              let model = buildModel (Some "4.4.6") resources []
              match effectReachability model "Mixed" |> Option.get |> _.reachability with
              | DataExplicit evidence ->
                  Expect.isTrue
                      (evidence |> List.exists (fun item -> item.kind = EffectFileSelection))
                      "the highest-certainty classification retains lower-certainty convention evidence"
              | other -> failtestf "the classification priority remains data_explicit, got %A" other

              match renamePolicy model "Mixed" with
              | RenameDenied reason ->
                  Expect.stringContains reason "renderer-convention" "rename denial explains the remaining ABI risk"
              | other -> failtestf "mixed explicit/effectFile evidence must deny rename, got %A" other
          }
          test "an ABI-forbidden Effect stays non-renamable even when it also has a direct caller" {
              let catalogText =
                  """{ "entries": [
                        { "game": "stellaris", "game_version": "4.4.6", "entry_kind": "effect", "name": "MixedAbi", "shader_file": "gfx/FX/mixed.shader", "evidence": "manual_runtime_test", "rename_policy": "forbidden" }
                     ] }"""

              let resources =
                  [ shaderResource "C:/mod/gfx/FX/mixed.shader" "gfx/FX/mixed.shader" (effectText "MixedAbi")
                    gfxResource "C:/mod/interface/mixed.gfx" "interface/mixed.gfx" "spriteType = { shader = MixedAbi }" ]

              let model = buildWithCatalog (Some "4.4.6") catalogText resources
              match (effectReachability model "MixedAbi" |> Option.get).reachability with
              | DataExplicit _ -> ()
              | other -> failtestf "textual classification remains data_explicit, got %A" other

              match renamePolicy model "MixedAbi" with
              | RenameDenied reason ->
                  Expect.stringContains reason "ABI catalog" "catalog denial takes precedence over textual renameability"
              | other -> failtestf "a forbidden active ABI entry must dominate direct caller evidence, got %A" other
          }
          test "engine_or_unreferenced is informational, never an error" {
              let resources =
                  [ shaderResource "C:/mod/gfx/FX/lonely.shader" "gfx/FX/lonely.shader" (effectText "LonelyEffect") ]

              let model = buildModel (Some "4.4.6") resources []

              let listed = allEffects model
              Expect.equal listed.Length 1 "allEffects lists the declared effect"

              let declaration, reachability = listed.Head
              Expect.equal declaration.name "LonelyEffect" "declared effect name"
              Expect.equal reachability EngineOrUnreferenced "classification"
              Expect.equal (reachabilityConfidence reachability) "unknown" "unknown confidence, not an error"

              match renamePolicy model "LonelyEffect" with
              | RenameRequiresExplicitForce _ -> ()
              | other -> failtestf "engine_or_unreferenced must not be denied as dead code, got %A" other
          } ]

[<Tests>]
let shaderRuntimeCompareTests =
    testList
        "pdx shader runtime vanilla comparison"
        [ test "workspace effect overrides the vanilla declaration" {
              let resources =
                  [ contentResource "vanilla" "C:/vanilla/gfx/FX/shared.shader" "gfx/FX/shared.shader" (effectText "SharedEffect")
                    shaderResource "C:/mod/gfx/FX/shared.shader" "gfx/FX/shared.shader" (effectText "SharedEffect") ]

              let model = buildModel (Some "4.4.6") resources []
              let comparison = compareWithVanilla model "SharedEffect"

              Expect.equal comparison.effective.Length 1 "one effective declaration"
              Expect.equal comparison.effective.Head.origin PdxShaderProject.Workspace "the mod copy is effective"
              Expect.equal comparison.overriddenVanilla.Length 1 "the vanilla copy is overridden"
              Expect.equal comparison.overriddenVanilla.Head.origin PdxShaderProject.Vanilla "overridden origin"
          }
          test "same Effect name in a different logical file is not treated as an override" {
              let resources =
                  [ contentResource "vanilla" "C:/vanilla/gfx/FX/a.shader" "gfx/FX/a.shader" (effectText "SharedEffect")
                    contentResource "vanilla" "C:/vanilla/gfx/FX/b.shader" "gfx/FX/b.shader" (effectText "SharedEffect")
                    shaderResource "C:/mod/gfx/FX/a.shader" "gfx/FX/a.shader" (effectText "SharedEffect") ]

              let model = buildModel (Some "4.4.6") resources []
              let comparison = compareWithVanilla model "SharedEffect"

              Expect.equal comparison.effective.Length 2 "one effective declaration remains for each logical shader file"
              Expect.equal comparison.overriddenVanilla.Length 1 "only vanilla a.shader is overridden"
              Expect.equal comparison.overriddenVanilla.Head.logicalPath "gfx/FX/a.shader" "b.shader is not an override candidate"
          } ]

[<Tests>]
let shaderProjectScannerTests =
    testList
        "pdx shader project scanner"
        [ test "Includes uses brace depth and ignores escaped-quote string lookalikes" {
              let text =
                  "name = \"prefix \\\" Includes = { \\\"fake.fxh\\\" }\"\nIncludes = { \"a.fxh\" nested = { \"not-direct.fxh\" } \"b.fxh\" }\n"

              let snapshot =
                  PdxShaderProject.createSnapshot
                      PdxShaderProject.Workspace
                      "C:/mod/gfx/FX/main.shader"
                      "gfx/FX/main.shader"
                      text

              let includes = PdxShaderProject.extractIncludes snapshot |> List.map _.target
              Expect.equal includes [ "a.fxh"; "b.fxh" ] "only direct strings in the balanced Includes block are targets"
          } ]
