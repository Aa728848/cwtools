module FolderValidationTests

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
open CWTools.Validation.Stellaris
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




open Tests
[<Tests>]
let folderTests =
    testList
        "validation"
        [ testFolder "./testfiles/validationtests/gfxtests" "gfx" false false "" false false 1 "en-GB"
          testFolder
              "./testfiles/validationtests/eventtests"
              "events"
              true
              false
              stellarisConfigRoot.Value
              false
              false
              1
              "en-GB"
          testFolder
              "./testfiles/multiplemodtests"
              "multiple"
              true
              true
              "./testfiles/multiplemodtests/test.cwt"
              false
              false
              1
              "en-GB"
          testFolder
              "./testfiles/configtests/validationtests"
              "configrules"
              true
              true
              "./testfiles/configtests/config/"
              false
              false
              1
              "en-GB"
          testFolder
              "./testfiles/configtests/validationtests"
              "configrules"
              true
              true
              "./testfiles/configtests/config/"
              false
              false
              1
              "ru-RU" ]

[<Tests>]
let stlSubfolderTests =
    testList "validation stl" (testSubdirectories 1 true "./testfiles/configtests/rulestests/STL" |> List.ofSeq)

[<Tests>]
let stlGlobalSubfolderTests =
    testList
        "validation stl global"
        (testSubdirectories 1 false "./testfiles/configtests/ruleswithglobaltests/STL"
         |> List.ofSeq)

[<Tests>]
let economicCategoryAIBudgetRegressionTests =
    let makeEntity logicalpath text =
        match CKParser.parseString text logicalpath with
        | Success(statements, _, _) ->
            let node = STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile logicalpath) statements

            { filepath = logicalpath
              logicalpath = logicalpath
              rawEntity = node
              entity = node
              validate = true
              entityType = EntityType.Other
              overwrite = Overwrite.No }
        | Failure(error, _, _) -> failwith error

    let makeSet entities =
        entities
        |> List.map (fun entity ->
            struct (
                entity,
                lazy (STLComputedData(None, None, None, false, None, None, None))
            ))
        |> EntitySet

    testList
        "economic category ai budget regression"
        [ testCase "uses existing parent chain when validating a changed economic category"
          <| fun _ ->
              let oldCategories =
                  makeEntity
                      "game/common/economic_categories/00_planet_jobs.txt"
                      "planet_jobs = {}\n\
                       planet_jobs_specialist = { parent = planet_jobs }"

              let oldBudget =
                  makeEntity "game/common/ai_budget/00_jobs.txt" "job_budget = { category = planet_jobs }"

              let newCategory =
                  makeEntity
                      "mod/common/economic_categories/kuat_eco_cate.txt"
                      "planet_researchers = { parent = planet_jobs_specialist }"

              let result =
                  CWTools.Validation.Stellaris.STLValidation.validateEconomicCatAIBudget
                      Unchecked.defaultof<_>
                      (makeSet [ oldCategories; oldBudget ])
                      (makeSet [ newCategory ])

              Expect.equal result OK "Parent chains from existing entities should satisfy AI budget lookup" ]

[<Tests>]
let scriptedActionValidationRegressionTests =
    let makeEntity logicalpath text =
        match CKParser.parseString text logicalpath with
        | Success(statements, _, _) ->
            let node = STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile logicalpath) statements

            { filepath = logicalpath
              logicalpath = logicalpath
              rawEntity = node
              entity = node
              validate = true
              entityType = EntityType.Other
              overwrite = Overwrite.No }
        | Failure(error, _, _) -> failwith error

    let makeSet entities =
        entities
        |> List.map (fun entity ->
            struct (
                entity,
                lazy (STLComputedData(None, None, None, false, None, None, None))
            ))
        |> EntitySet

    let validate text =
        let file = makeEntity "mod/common/scripted_actions/test_actions.txt" text

        CWTools.Validation.Stellaris.STLValidation.validateScriptedActionScopeOrder
            (makeSet [])
            (makeSet [ file ])

    testList
        "scripted action validation regression"
        [ testCase "allows user_scope before scope on previous line"
          <| fun _ ->
              let result =
                  validate
                      "good_action = {\n\
                       \tuser_scope = fleet\n\
                       \tscope = planet\n\
                       }"

              Expect.equal result OK "user_scope before scope should be valid"

          testCase "allows user_scope before scope on the same line"
          <| fun _ ->
              let result = validate "good_action = { user_scope = fleet scope = planet }"
              Expect.equal result OK "same-line user_scope before scope should be valid"

          testCase "allows comments before required first entries"
          <| fun _ ->
              let result =
                  validate
                      "good_action = {\n\
                       \t# Action scope setup\n\
                       \tuser_scope = fleet\n\
                       \tscope = planet\n\
                       }"

              Expect.equal result OK "comments should not count as scripted_action entries"

          testCase "reports scope before user_scope"
          <| fun _ ->
              let result =
                  validate
                      "bad_action = {\n\
                       \tscope = planet\n\
                       \tuser_scope = fleet\n\
                       }"

              match result with
              | Invalid(_, errors) ->
                  Expect.equal errors.Length 1 "Only the ordering diagnostic should be reported"
                  Expect.equal
                      errors.Head.message
                      "In scripted_action, user_scope must be the first entry and scope must be the second entry"
                      "Diagnostic message should explain the required order"
                  Expect.equal errors.Head.range.StartLine 2 "Diagnostic should be placed on the early scope line"
              | OK -> failtest "Expected scripted_action scope ordering diagnostic"

          testCase "reports scope not being the second entry"
          <| fun _ ->
              let result =
                  validate
                      "bad_action = {\n\
                       \tuser_scope = fleet\n\
                       \ttooltip = BAD_ACTION_TOOLTIP\n\
                       \tscope = planet\n\
                       }"

              match result with
              | Invalid(_, errors) ->
                  Expect.equal errors.Length 1 "Only the ordering diagnostic should be reported"
                  Expect.equal
                      errors.Head.message
                      "In scripted_action, user_scope must be the first entry and scope must be the second entry"
                      "Diagnostic message should explain the required order"
                  Expect.equal errors.Head.range.StartLine 3 "Diagnostic should be placed on the second entry"
              | OK -> failtest "Expected scripted_action scope ordering diagnostic" ]

[<Tests>]
let inlineScriptCompletionRegressionTests =
    testSequenced
    <| testList
        "inline script completion regression"
        [ testWithCapturedLogs "unicode inline script paths survive loading and indexing" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let scriptName = "districts/精灵服务区划岗位添加（无海军）"

              let inlineFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "districts", "精灵服务区划岗位添加（无海军）.txt")
                  )

              let callerFilename =
                  Path.GetFullPath(Path.Combine(folder, "common", "script_consume", "中文调用者.txt"))

              stl.UpdateFile false inlineFilename (Some "expected_leaf = yes") |> ignore
              let callerErrors =
                  stl.UpdateFile false callerFilename (Some $"inline_script = {{ script = {scriptName} }}")

              Expect.isFalse
                  (callerErrors |> List.exists (fun error -> error.message.Contains("Missing inline_script")))
                  "Unicode inline_script paths should expand without a missing-script diagnostic"

              let versionBeforeCallerRefresh = ResourceManagerEager.currentVersion ()
              let callers = stl.RefreshInlineScriptCallers [ scriptName + ".txt" ]
              Expect.contains callers callerFilename "Unicode inline_script references should remain indexable"
              Expect.isGreaterThan
                  (ResourceManagerEager.currentVersion ())
                  versionBeforeCallerRefresh
                  "Replacing expanded caller entities should invalidate resource-versioned semantic snapshots"

          testWithCapturedLogs "hash parameter comments out expanded inline entries" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>

              let inlineFilename =
                  Path.GetFullPath(Path.Combine(folder, "common", "inline_scripts", "hash_parameter_comment.txt"))

              let callerFilename =
                  Path.GetFullPath(Path.Combine(folder, "common", "script_consume", "hash_parameter_comment.txt"))

              stl.UpdateFile
                  false
                  inlineFilename
                  (Some
                      "root_only = yes
                       $NO_EVENT$unexpected_entry = yes")
              |> ignore

              let callerErrors =
                  stl.UpdateFile
                      false
                      callerFilename
                      (Some
                          "inline_script = {
                               script = hash_parameter_comment
                               NO_EVENT = \"#\"
                           }")

              let unexpectedErrors =
                  callerErrors
                  |> List.filter (fun error ->
                      error.code = "CW274"
                      || error.message.Contains("unexpected_entry", StringComparison.OrdinalIgnoreCase))

              Expect.isEmpty
                  unexpectedErrors
                  $"A # inline parameter on its own line should comment out the substituted template entry, got %A{unexpectedErrors}"

          testWithCapturedLogs "nested inline evaluates arithmetic script path suffixes" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let varsFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "scripted_variables", "inline_path_arithmetic.txt")
                  )
              let parentInlineFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "inline_path_arithmetic_parent.txt")
                  )
              let switchInlineFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "inline_path_arithmetic_switch.txt")
                  )
              let caseZeroFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "inline_path_arithmetic_case_0.txt")
                  )
              let caseOneFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "inline_path_arithmetic_case_1.txt")
                  )
              let callerFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "script_consume", "inline_path_arithmetic.txt")
                  )

              stl.UpdateFile false varsFilename (Some "@inline_path_toggle = 0")
              |> ignore
              stl.UpdateFile
                  false
                  parentInlineFilename
                  (Some
                      "inline_script = {
                           script = inline_path_arithmetic_switch
                           file = inline_path_arithmetic_case_
                           value = @[ $toggle$ ]
                           params = \"root_only = yes\"
                       }")
              |> ignore
              stl.UpdateFile
                  false
                  switchInlineFilename
                  (Some
                      "inline_script = {
                           script = $file$$value$
                           $params$
                       }")
              |> ignore
              stl.UpdateFile false caseZeroFilename (Some "# no-op")
              |> ignore
              stl.UpdateFile false caseOneFilename (Some "$params$")
              |> ignore

              let callerErrors =
                  stl.UpdateFile
                      false
                      callerFilename
                      (Some
                          "inline_path_arithmetic = {
                               inline_script = {
                                   script = inline_path_arithmetic_parent
                                   toggle = @inline_path_toggle
                               }
                           }")

              Expect.isFalse
                  (callerErrors |> List.exists (fun error -> error.message.Contains("Missing inline_script")))
                  "Arithmetic inline_script path suffixes should resolve to a concrete inline script"

          testWithCapturedLogs "nested inline keeps concrete parent path" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "completion_inner.txt")
                  )
              let filetext = File.ReadAllText filename

              let labels =
                  stl.Complete (mkPos 2 8) filename filetext
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.contains labels "expected_leaf" "Nested inline completion should use the concrete child block"
              Expect.isFalse (labels |> List.contains "root_only") "Nested inline completion should not fall back to root fields"

              let eventFragmentFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "events", "event_fragment.txt")
                  )
              let eventFragmentText = File.ReadAllText(eventFragmentFilename).TrimEnd() + "\n"
              let eventRootLabels =
                  stl.Complete
                      (mkPos (eventFragmentText.Split('\n').Length) 0)
                      eventFragmentFilename
                      eventFragmentText
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.contains eventRootLabels "option" "Completion after a closed inline option should return event-root fields"
              Expect.isFalse (eventRootLabels |> List.contains "test") "Completion after a closed inline option must not stay inside that option"

              let parameterizedFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "completion_param_common.txt")
                  )

              let parameterizedFiletext = File.ReadAllText parameterizedFilename

              let parameterizedLabels =
                  stl.Complete (mkPos 1 4) parameterizedFilename parameterizedFiletext
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.contains parameterizedLabels "expected_leaf" "Parameterized nested inline completion should use the concrete child block"
              Expect.isFalse (parameterizedLabels |> List.contains "root_only") "Parameterized nested inline completion should not fall back to root fields"

              let inlineDefaultFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "completion_pipe_default_no.txt")
                  )

              let inlineDefaultFiletext = File.ReadAllText inlineDefaultFilename

              let inlineDefaultLabels =
                  stl.Complete (mkPos 1 4) inlineDefaultFilename inlineDefaultFiletext
                  |> List.map (function
                      | Simple(label, _, _)
                      | Detailed(label, _, _, _)
                      | Snippet(label, _, _, _, _) -> label)

              Expect.isFalse (inlineDefaultLabels |> List.contains "expected_leaf") "Inline script callers should not match path defaults with pipe syntax"

          testWithCapturedLogs "nested inline resolves string scripted variable suffixes" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let varsFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "scripted_variables", "suffix_variable_regression.txt")
                  )
              let parentInlineFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "suffix_variable_parent.txt")
                  )
              let childInlineFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "suffix_variable_child.txt")
                  )
              let callerFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "script_consume", "suffix_variable_regression.txt")
                  )

              stl.UpdateFile
                  false
                  varsFilename
                  (Some
                      "@target_base = 0
                       @target_base_suffix = 1
                       @suffix_var = \"_suffix\"")
              |> ignore
              stl.UpdateFile
                  false
                  parentInlineFilename
                  (Some
                      "inline_script = {
                           script = suffix_variable_child
                           TARGET_SUFFIX = $TARGET_SUFFIX$
                       }")
              |> ignore
              stl.UpdateFile
                  false
                  childInlineFilename
                  (Some
                      "country_event = {
                           not_event = @target_base$TARGET_SUFFIX|\"\"$
                       }")
              |> ignore
              stl.UpdateFile
                  false
                  callerFilename
                  (Some
                      "suffix_variable_regression = {
                           inline_script = {
                               script = suffix_variable_parent
                               TARGET_SUFFIX = @suffix_var
                           }
                       }")
              |> ignore

              let diagnostics = stl.ValidationErrors()
              let unresolvedSuffixErrors =
                  diagnostics
                  |> List.filter (fun error ->
                      error.code = "CW101"
                      && error.message.Contains("@target_base@suffix_var"))

              Expect.isEmpty
                  unresolvedSuffixErrors
                  "Nested inline parameters should resolve string scripted variables before CW101 lookup"

          testWithCapturedLogs "parameterized inline CW101 expressions keep call-site provenance" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/inlinescripts"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let inlineFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "inline_scripts", "parameter_variable_regression.txt")
                  )
              let callerFilename =
                  Path.GetFullPath(
                      Path.Combine(folder, "common", "script_consume", "parameter_variable_regression.txt")
                  )

              let inlineText =
                  "country_event = {
                       not_event = @$VARIABLE$
                       not_event = @[ expression_$VARIABLE$ + 1 ]
                   }
                   inline_script = root_inline"

              stl.UpdateFile false inlineFilename (Some inlineText)
              |> ignore
              stl.UpdateFile
                  false
                  callerFilename
                  (Some
                      "parameter_variable_regression = { inline_script = { script = parameter_variable_regression VARIABLE = missing_variable } }")
              |> ignore

              let assertParameterErrors phase diagnostics =
                  for expectedVariable in [ "@missing_variable"; "@expression_missing_variable" ] do
                      let parameterError =
                          diagnostics
                          |> List.tryFind (fun error ->
                              error.code = "CW101"
                              && error.message = $"{expectedVariable} is not defined"
                              && String.Equals(
                                  Path.GetFullPath(error.range.FileName),
                                  inlineFilename,
                                  StringComparison.OrdinalIgnoreCase
                              ))

                      Expect.isSome
                          parameterError
                          $"{phase}: expanded inline parameters should produce the concrete CW101 for {expectedVariable}"
                      let related = parameterError.Value.relatedErrors |> Option.defaultValue []
                      Expect.exists
                          related
                          (fun item ->
                              item.message = "Related source"
                              && String.Equals(
                                  Path.GetFullPath(item.location.FileName),
                                  callerFilename,
                                  StringComparison.OrdinalIgnoreCase
                              ))
                          $"{phase}: parameterized CW101 for {expectedVariable} should be owned by dynamic call-site validation"

              assertParameterErrors "initial validation" (stl.ValidationErrors())

              // Dynamic diagnostics are displayed at the definition range, while
              // their Related source identifies the entity that must be revalidated.
              let batchDiagnostics =
                  stl.ValidateFilesLocalCancellable(
                      [ inlineFilename; callerFilename ],
                      (fun () -> false)
                  )
                  |> Option.defaultWith (fun () -> failtest "local batch validation was unexpectedly cancelled")
              assertParameterErrors "batched file validation" batchDiagnostics

              // Mirror the server's Ctrl+S path: update the definition, rebuild
              // all indexed callers, refresh rules, warm dynamic data, then run
              // the deferred full validation pass.
              stl.UpdateFile false inlineFilename (Some inlineText) |> ignore
              let refreshedCallers = stl.RefreshInlineScriptCallers [ "parameter_variable_regression.txt" ]
              Expect.contains refreshedCallers callerFilename "Save refresh should find the inline caller"
              stl.RefreshCaches()
              stl.ForceDynamicParameterData(2000, 2000) |> ignore
              assertParameterErrors "post-save deferred validation" (stl.ValidationErrors())

          testWithCapturedLogs "inline save does not incrementally drop caller-generated type ids" <| fun () ->
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-inline-generated-types-" + Guid.NewGuid().ToString("N"))

              try
                  let inlineDir = Path.Combine(folder, "common", "inline_scripts", "generated")
                  let callerDir = Path.Combine(folder, "common", "starbase_modules")
                  Directory.CreateDirectory inlineDir |> ignore
                  Directory.CreateDirectory callerDir |> ignore

                  let inlineFilename = Path.Combine(inlineDir, "module.txt")
                  let callerFilename = Path.Combine(callerDir, "caller.txt")
                  let inlineText = "$TYPE$_module = { on_destroyed = { has_starbase_module = $TYPE$_module } }"
                  let callerText = "inline_script = { script = generated/module TYPE = demo }"

                  File.WriteAllText(inlineFilename, inlineText)
                  File.WriteAllText(callerFilename, callerText)

                  let rules =
                      "types = {
                           type[starbase_module] = {
                               path = \"game/common/starbase_modules\"
                           }
                       }
                       starbase_module = {
                           on_destroyed = {
                               has_starbase_module = <starbase_module>
                           }
                       }"

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = [ "inline-generated-types.cwt", rules ]
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>

                  let assertNoGeneratedTypeError phase =
                      let errors = stl.ValidateFile false callerFilename
                      let generatedTypeErrors =
                          errors
                          |> List.filter (fun error ->
                              error.code = "CW274"
                              || error.message.Contains("Expected value of type starbase_module, got 'demo_module'"))

                      Expect.isEmpty
                          generatedTypeErrors
                          $"{phase}: caller-generated type IDs should stay available to inline validation, got %A{generatedTypeErrors}"

                  assertNoGeneratedTypeError "initial validation"

                  stl.UpdateFile false inlineFilename (Some inlineText) |> ignore
                  let staged = stl.PrepareScriptedTypes([ inlineFilename ], false)
                  Expect.isNone staged "Inline script templates depend on callers and must fall back to full type refresh"

                  let refreshedCallers = stl.RefreshInlineScriptCallers [ "generated/module.txt" ]
                  Expect.contains refreshedCallers callerFilename "Save refresh should find the caller that expands the inline template"
                  stl.RefreshCaches()

                  assertNoGeneratedTypeError "post-save refresh"
              finally
                  if Directory.Exists folder then
                      Directory.Delete(folder, true) ]

[<Tests>]
let scriptedBracketParameterRegressionTests =
    let cursorAtMarker (text: string) =
        let marker = text.IndexOf('|')
        Expect.isGreaterThan marker -1 "test cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let cursorAtTildeMarker (text: string) =
        let marker = text.IndexOf('~')
        Expect.isGreaterThan marker -1 "test cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let label =
        function
        | Simple(label, _, _)
        | Detailed(label, _, _, _)
        | Snippet(label, _, _, _, _) -> label

    testSequenced
    <| testList
        "scripted bracket parameter regression"
        [ testWithCapturedLogs "bracket params feed call-site completion" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripteddefaults"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    option = {
        scripted_effect_bracket_param_validation = {
            |
        }
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "bracket_condition" "Positive bracket condition should complete as a scripted parameter"
              Expect.contains labels "negated_condition" "Negated bracket condition should complete as a scripted parameter"

              let prefixedFiletext, prefixedPos =
                  cursorAtMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    option = {
        scripted_effect_bracket_prefixed_param_validation = {
            |
        }
    }
}
"""

              let prefixedLabels = stl.Complete prefixedPos filename prefixedFiletext |> List.map label

              Expect.contains prefixedLabels "kamikakushi_bonus" "Prefixed bracket condition should complete as a scripted parameter"

          testWithCapturedLogs "scripted effect definition body does not complete own call-site params" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext =
                  configFilesFromDir folder
                  @ [ "scripted_effect_completion.cwt", "scripted_effect = { alias_name[effect] = alias_match_left[effect] }" ]

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
test_scripted_effect_params = {
    |
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.isFalse (labels |> List.contains "test_lhs") "A scripted effect definition body should not be treated as a call-site parameter block"
              Expect.isFalse (labels |> List.contains "test_rhs") "A scripted effect definition body should keep normal effect completion"
              Expect.contains labels "set_ship_flag" (sprintf "A scripted effect definition body should complete normal effects, got %A" (labels |> List.truncate 50))

          testWithCapturedLogs "scripted effect definition tail completes normal effects" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext =
                  configFilesFromDir folder
                  @ [ "scripted_effect_completion.cwt", "scripted_effect = { alias_name[effect] = alias_match_left[effect] }" ]

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    set_country_flag = yes
    s|
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "set_ship_flag" (sprintf "A scripted effect definition body tail should complete normal effects, got %A" (labels |> List.truncate 50))

          testWithCapturedLogs "scripted effect definition body completion survives preceding effects" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let completionRule =
                  "scripted_effect = {\n    optimize_memory\n    alias_name[effect] = alias_match_left[effect]\n}"
              let configtext =
                  configFilesFromDir folder
                  @ [ "scripted_effect_completion.cwt", completionRule ]

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let afterBatch =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    set_spawn_system_batch = begin
    s|
}
"""

              let afterOrdinaryEffect =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    set_country_flag = yes
    |
}
"""

              let afterUnknownScalarEffect =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    unknown_effect = yes
    s|
}
"""

              let afterOrdinaryPartial =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    set_country_flag = yes
    s|
}
"""

              let afterBeginValue =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    set_country_flag = begin
    s|
}
"""

              let afterOptimizeMemory =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    optimize_memory
    if = {
        limit = { always = yes }
    }
    s|
}
"""

              let results =
                  [ "ordinary-partial", afterOrdinaryPartial
                    "batch", afterBatch
                    "ordinary", afterOrdinaryEffect
                    "unknown-scalar", afterUnknownScalarEffect
                    "begin-value", afterBeginValue
                    "optimize-memory", afterOptimizeMemory ]
                  |> List.map (fun (caseName, (filetext, pos)) ->
                      caseName, (stl.Complete pos filename filetext |> List.map label))
              let failures =
                  results
                  |> List.filter (fun (_, labels) -> not (labels |> List.contains "set_ship_flag"))

              Expect.isEmpty failures (sprintf "Every scripted effect definition-body slot should retain effect completion, got %A" (failures |> List.map (fun (name, labels) -> name, labels |> List.truncate 50)))

          testWithCapturedLogs "scripted definition bodies complete effects and triggers from full rules" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let docsPath = (Path.Combine(stellarisConfigRoot.Value, "config", "logs", "trigger_docs.log"))
              let configtext =
                  (docsPath, File.ReadAllText docsPath)
                  :: configFilesFromDir stellarisConfigRoot.Value

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let cases =
                  [ "empty", "test_scripted_effect_none = {\n    |\n}"
                    "partial", "test_scripted_effect_none = {\n    no|\n}"
                    "after-effect", "test_scripted_effect_none = {\n    set_country_flag = yes\n    no|\n}"
                    "after-batch", "test_scripted_effect_none = {\n    set_spawn_system_batch = begin\n    no|\n}"
                    "after-optimize-memory-empty", "test_scripted_effect_none = {\n    optimize_memory\n    |\n}"
                    "after-optimize-memory-partial", "test_scripted_effect_none = {\n    optimize_memory\n    no|\n}"
                    "after-optimize-memory-and-block", "test_scripted_effect_none = {\n    optimize_memory\n    if = { limit = { always = yes } }\n    no|\n}" ]

              let failures =
                  cases
                  |> List.map (fun (caseName, markedText) ->
                      let filetext, pos = cursorAtMarker markedText
                      caseName, (stl.Complete pos filename filetext |> List.map label))
                  |> List.filter (fun (_, labels) -> not (labels |> List.contains "set_country_flag"))

              Expect.isEmpty failures (sprintf "Every scripted effect definition body should complete effects from the full rules, got %A" (failures |> List.map (fun (name, labels) -> name, labels |> List.truncate 50)))

              let triggerFilename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let triggerText, triggerPos =
                  cursorAtMarker
                      "test_scripted_trigger_none = {\n    optimize_memory\n    ha|\n}"
              let triggerLabels = stl.Complete triggerPos triggerFilename triggerText |> List.map label

              Expect.contains triggerLabels "has_country_flag" (sprintf "A scripted trigger definition body should complete triggers from the full rules, got %A" (triggerLabels |> List.truncate 50))

          testWithCapturedLogs "scripted effect file root completion stays at definition level" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))

              let emptyFiletext, emptyPos =
                  cursorAtMarker
                      """
existing_scripted_effect = {
    set_ship_flag = yes
}
|
"""

              let partialFiletext, partialPos =
                  cursorAtMarker
                      """
existing_scripted_effect = {
    set_ship_flag = yes
}
s|
"""

              for filetext, pos in [ emptyFiletext, emptyPos; partialFiletext, partialPos ] do
                  let labels = stl.Complete pos filename filetext |> List.map label

                  Expect.contains labels "scripted_effect" (sprintf "File-root completion should offer the definition type, got %A" (labels |> List.truncate 50))
                  Expect.isFalse (labels |> List.contains "set_ship_flag") "File-root completion must not leak fields from the preceding definition body"

          testWithCapturedLogs "nested scripted effect calls inside definitions still complete params" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
test_scripted_effect_none = {
    test_scripted_effect_params = {
        |
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "test_lhs" "Nested scripted effect calls inside definition files should still complete call-site params"
              Expect.contains labels "test_rhs" "Nested scripted effect calls inside definition files should still complete all declared params"

          testWithCapturedLogs "incremental scripted effect calls resolve same-file variables" <| fun () ->
              let configFolder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-scripted-effect-local-vars-" + Guid.NewGuid().ToString("N"))

              try
                  let effectsDir = Path.Combine(folder, "common", "scripted_effects")
                  let eventsDir = Path.Combine(folder, "events")
                  Directory.CreateDirectory effectsDir |> ignore
                  Directory.CreateDirectory eventsDir |> ignore

                  let effectsFilename = Path.Combine(effectsDir, "effects.txt")
                  let sameFileCaller = Path.Combine(eventsDir, "same_file.txt")
                  let otherVariableFile = Path.Combine(eventsDir, "other_variable.txt")
                  let crossFileCaller = Path.Combine(eventsDir, "cross_file.txt")
                  File.WriteAllText(
                      effectsFilename,
                      "test_scripted_effect_variable_param = { set_country_flag = $FRACTION$ }"
                  )
                  File.WriteAllText(
                      sameFileCaller,
                      "namespace = test\ncountry_event = { is_triggered_only = yes }"
                  )
                  File.WriteAllText(
                      otherVariableFile,
                      "@OTHER_FILE_FRACTION = 0.4\nnamespace = other\ncountry_event = { is_triggered_only = yes }"
                  )
                  File.WriteAllText(
                      crossFileCaller,
                      "namespace = cross\ncountry_event = { is_triggered_only = yes option = { test_scripted_effect_variable_param = { FRACTION = @OTHER_FILE_FRACTION } } }"
                  )

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = configFilesFromDir configFolder
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let updatedSameFile =
                      "@MANDALORIAN_FLEET_FRACTION = 0.3\nnamespace = test\ncountry_event = { is_triggered_only = yes option = { test_scripted_effect_variable_param = { FRACTION = @MANDALORIAN_FLEET_FRACTION } } }"
                  let staged = stl.PrepareUpdateFileInteractive sameFileCaller (Some updatedSameFile)
                  Expect.isTrue
                      (stl.CommitUpdateFileInteractive staged)
                      "The editor update should commit before validation"
                  let incrementalDiagnostics =
                      stl.ValidateFile false sameFileCaller
                  let diagnostics = incrementalDiagnostics @ stl.ValidationErrors()

                  let expandedUndefinedErrors filename variable =
                      diagnostics
                      |> List.filter (fun error ->
                          error.code = "CW101"
                          && error.message.Contains($"{variable} is not defined")
                          && String.Equals(
                              Path.GetFullPath(error.range.FileName),
                              Path.GetFullPath(filename),
                              StringComparison.OrdinalIgnoreCase
                          ))

                  Expect.isEmpty
                      (expandedUndefinedErrors sameFileCaller "@MANDALORIAN_FLEET_FRACTION")
                      "A scripted effect call should resolve @variables from its caller file"
                  Expect.isNonEmpty
                      (expandedUndefinedErrors crossFileCaller "@OTHER_FILE_FRACTION")
                      "A file-local @variable from another file must not satisfy a scripted effect call"
              finally
                  if Directory.Exists folder then
                      Directory.Delete(folder, true)

          testWithCapturedLogs "script value bracket params feed value completion" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:scripted_bracket_positive|~
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "BRACKET" "Script value bracket condition should complete as a value parameter"

          testWithCapturedLogs "script value names complete after value prefix" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:~
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains labels "value:scripted_param" "Script values should complete after value:"
              Expect.contains labels "value:scripted_bracket_positive" "Script value names should include bracket-param definitions"

          testWithCapturedLogs "script value param completion skips value slot" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:scripted_param|PARAM|~
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.isFalse (labels |> List.contains "PARAM") "Script value value slots should not suggest parameter names"

          testWithCapturedLogs "script value parameterized call goes to definition" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        test_value = value:scri~pted_param|PARAM|abs|
    }
}
"""

              let target = stl.GoToType pos filename filetext

              Expect.isSome target "Parameterized script value call should go to its definition"
              Expect.stringContains
                  (target.Value.FileName.Replace("\\", "/"))
                  "common/script_values/test.txt"
                  "Go to definition should target the script_values file"

          testWithCapturedLogs "script value in effect count goes to definition" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtTildeMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    option = {
        while = {
            count = value:scri~pted_param|PARAM|abs|
        }
    }
}
"""

              let target = stl.GoToType pos filename filetext

              Expect.isSome target "Script value count in an effect block should go to its definition"
              Expect.stringContains
                  (target.Value.FileName.Replace("\\", "/"))
                  "common/script_values/test.txt"
                  "Go to definition should target the script_values file"

          testWithCapturedLogs "scripted count wrapper completes as trigger" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let filename = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let filetext, pos =
                  cursorAtMarker
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        |
    }
}
"""

              let labels = stl.Complete pos filename filetext |> List.map label

              Expect.contains
                  labels
                  "test_scripted_trigger_value"
                  "Scripted triggers wrapping count_* without count should complete as trigger conditions" ]

[<Tests>]
let goToDefinitionRegressionTests =
    let cursorAtTildeMarker (text: string) =
        let marker = text.IndexOf('~')
        Expect.isGreaterThan marker -1 "test cursor marker was not found"
        let before = text.Substring(0, marker)
        let line = (before |> Seq.filter ((=) '\n') |> Seq.length) + 1
        let lastLineBreak = before.LastIndexOf('\n')
        let column = if lastLineBreak < 0 then marker else marker - lastLineBreak - 1
        text.Remove(marker, 1), mkPos line column

    let writeFile (path: string) (text: string) =
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, text.TrimStart().Replace("\r\n", "\n"))

    testSequenced
    <| testList
        "go to definition regressions"
        [ testWithCapturedLogs "carrier_event id resolves event.carrier definitions" <| fun () ->
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-carrier-event-goto-" + Guid.NewGuid().ToString("N"))

              try
                  let eventPath = Path.Combine(folder, "events", "carrier_events.txt")

                  let filetext, pos =
                      cursorAtTildeMarker
                          """
namespace = carrier_goto

carrier_event = {
    id = carrier_goto.1
    hide_window = yes
    is_triggered_only = yes
}

country_event = {
    id = carrier_goto.2
    hide_window = yes
    is_triggered_only = yes
    immediate = {
        carrier_event = { id = carrier_goto.~1 }
    }
}
"""

                  writeFile eventPath filetext

                  let configtext = configFilesFromDir stellarisConfigRoot.Value

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = configtext
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let target = stl.GoToType pos eventPath filetext

                  Expect.isSome target "carrier_event should go to the carrier event definition"
                  Expect.equal
                      (Path.GetFullPath(target.Value.FileName))
                      (Path.GetFullPath(eventPath))
                      "Go to definition should target the defining event file"
              finally
                  if Directory.Exists folder then
                      Directory.Delete(folder, true)

          testWithCapturedLogs "right-hand scripted variable does not resolve as the left-hand typed key" <| fun () ->
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-scripted-variable-goto-" + Guid.NewGuid().ToString("N"))

              try
                  let componentPath = Path.Combine(folder, "common", "component_templates", "test.txt")

                  let filetext, pos =
                      cursorAtTildeMarker
                          """
@s_t2_cost = 15

sr_parts_adf = {
    size = medium
    type = weapon
    resources = {
        category = ship_components
        cost = {
            sr_parts_adf = @s_t2_~cost
        }
    }
}
"""

                  writeFile componentPath filetext

                  let configtext = configFilesFromDir stellarisConfigRoot.Value

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = configtext
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let target = stl.GoToType pos componentPath filetext

                  Expect.isSome target "The right-hand scripted variable should resolve"
                  Expect.equal
                      target.Value.StartLine
                      1
                      "The right-hand token should resolve to the scripted-variable definition, not the left-hand component"
              finally
                  if Directory.Exists folder then
                      Directory.Delete(folder, true) ]

[<Tests>]
let scriptedTriggerOrValidationSeverityTests =
    let writeFile (path: string) (text: string) =
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, text.TrimStart().Replace("\r\n", "\n"))

    testSequenced
    <| testList
        "scripted trigger OR validation severity"
        [ testWithCapturedLogs "call-site errors inside OR branches are warnings" <| fun () ->
              let folder =
                  Path.Combine(Path.GetTempPath(), "cwtools-scripted-or-severity-" + Guid.NewGuid().ToString("N"))

              try
                  let rulesPath = Path.Combine(folder, "rules.cwt")
                  let scriptedTriggersPath = Path.Combine(folder, "common", "scripted_triggers", "test.txt")
                  let eventPath = Path.Combine(folder, "events", "test.txt")

                  writeFile
                      rulesPath
                      """
types = {
    type[event] = {
        path = "game/events"
        subtype[country] = {
        }
    }
    type[scripted_trigger] = {
        path = "game/common/scripted_triggers"
    }
}

alias[trigger:<scripted_trigger>] = bool
alias[trigger:<scripted_trigger>] = {
    enum[scripted_effect_params] = scalar
    enum[scripted_effect_params] = scope_field
}
alias[trigger:has_country_flag] = bool
alias[trigger:OR] = { alias_name[trigger] = alias_match_left[trigger] }

event = {
    is_triggered_only = yes
    trigger = {
        alias_name[trigger] = alias_match_left[trigger]
    }
}

scripted_trigger = {
    alias_name[trigger] = alias_match_left[trigger]
}
"""

                  writeFile
                      scriptedTriggersPath
                      """
scripted_trigger_or_param = {
    OR = {
        has_country_flag = yes
        has_country_flag = $PARAM$
    }
}

scripted_trigger_plain_param = {
    has_country_flag = $PARAM$
}
"""

                  writeFile
                      eventPath
                      """
namespace = test

country_event = {
    is_triggered_only = yes
    trigger = {
        scripted_trigger_or_param = {
            PARAM = maybe
        }
        scripted_trigger_plain_param = {
            PARAM = maybe
        }
    }
}
"""

                  let settings =
                      { emptyStellarisSettings folder with
                          rules =
                              Some
                                  { ruleFiles = [ rulesPath, File.ReadAllText rulesPath ]
                                    validateRules = true
                                    debugRulesOnly = false
                                    debugMode = false } }

                  let stl = STLGame(settings) :> IGame<STLComputedData>
                  let diagnostics = stl.ValidationErrors()

                  let callSiteErrors =
                      diagnostics
                      |> List.filter (fun e ->
                          e.message.StartsWith("This call of scripted trigger", StringComparison.Ordinal))

                  let diagnosticSummary =
                      let scriptedTriggerTypes =
                          stl.Types()
                          |> Map.tryFind "scripted_trigger"
                          |> Option.map (Array.map (fun t -> t.id) >> String.concat ", ")
                          |> Option.defaultValue "<missing scripted_trigger type map>"

                      diagnostics
                      |> List.map (fun e -> $"{e.code} {e.severity}: {e.message}")
                      |> String.concat "\n"
                      |> fun errors -> $"scripted_trigger types: {scriptedTriggerTypes}\n{errors}"

                  let findCallSiteError (name: string) =
                      match callSiteErrors |> List.tryFind (fun e -> e.message.Contains(name)) with
                      | Some e -> e
                      | None -> failtest $"Expected scripted trigger call-site diagnostic for {name}, got:\n{diagnosticSummary}"

                  let orError = findCallSiteError "scripted_trigger_or_param"
                  let plainError = findCallSiteError "scripted_trigger_plain_param"

                  Expect.equal
                      orError.severity
                      Severity.Warning
                      "Invalid values under a scripted trigger OR branch should be reported as warnings at the call site"

                  Expect.equal
                      plainError.severity
                      Severity.Error
                      "Invalid values outside OR branches should remain call-site errors"
              finally
                  try
                      if Directory.Exists folder then
                          Directory.Delete(folder, true)
                  with _ ->
                      () ]

[<Tests>]
let incrementalScriptedRefreshTests =
    let stlScriptedGame () =
        let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
        let configtext = configFilesFromDir folder

        let settings =
            { emptyStellarisSettings folder with
                rules =
                    Some
                        { ruleFiles = configtext
                          validateRules = true
                          debugRulesOnly = false
                          debugMode = false } }

        STLGame(settings) :> IGame<STLComputedData>, folder

    // Sequenced: constructing an STLGame re-inits the global ScopeManager singleton, which
    // races with any other game construction running in parallel.
    testSequenced
    <| testList
        "incremental scripted refresh"
        [ testCase "same-file scripted-variable arithmetic is rejected while cross-file remains valid" <| fun () ->
              let parse path text =
                  match CKParser.parseString text path with
                  | Success(statements, _, _) -> STLProcess.shipProcess.ProcessNode () "root" (mkZeroFile path) statements
                  | Failure(error, _, _) -> failtest error

              let sameFile =
                  parse
                      "common/scripted_variables/same_file.txt"
                      "@base = 500000\n@derived = @[ base * 1.5 ]"
              let crossFile =
                  parse
                      "common/scripted_variables/derived_only.txt"
                      "@derived = @[ base * 1.5 ]"

              match STLValidation.sameFileScriptedVariableArithmeticErrors sameFile with
              | Invalid(_, [ error ]) ->
                  Expect.equal error.code "CW278" "the engine-incompatible same-file expression gets a dedicated error"
                  Expect.stringContains error.message "@derived" "the diagnostic identifies the derived constant"
                  Expect.stringContains error.message "@base" "the diagnostic identifies the same-file dependency"
              | result -> failtestf "expected one same-file arithmetic diagnostic, got %A" result

              Expect.equal
                  (STLValidation.sameFileScriptedVariableArithmeticErrors crossFile)
                  OK
                  "a dependency defined in another scripted_variables file remains legal"

          testCase "scripted-variable path ordering is platform-aware and total" <| fun () ->
              let upper = "common/scripted_variables/A.txt"
              let lower = "common/scripted_variables/a.txt"
              Expect.isLessThan
                  (ScriptedVariableContribution.comparePathForPlatform false upper lower)
                  0
                  "Unix ordering must preserve case and use ordinal order"
              Expect.isGreaterThan
                  (ScriptedVariableContribution.comparePathForPlatform false lower upper)
                  0
                  "Unix case-distinct paths must not compare equal"
              Expect.isLessThan
                  (ScriptedVariableContribution.comparePathForPlatform true upper lower)
                  0
                  "Windows ordering must case-fold, then use the original ordinal path as a deterministic tie-break"
              Expect.isGreaterThan
                  (ScriptedVariableContribution.comparePathForPlatform true lower upper)
                  0
                  "Windows case variants must not compare equal after the deterministic tie-break"
              Expect.equal
                  0
                  (ScriptedVariableContribution.comparePathForPlatform false "common\\scripted_variables\\a.txt" lower)
                  "separator variants of the same path may compare equal"

          testWithCapturedLogs "scripted-variable contribution-only stages track values names and paths" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let variableFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_variables", "incremental.txt"))
              let relativeFile = Path.GetRelativePath(Directory.GetCurrentDirectory(), variableFile)

              stl.UpdateFile false variableFile (Some "@incremental = one") |> ignore
              let added = stl.PrepareScriptedTypes([ variableFile ], false)
              Expect.isSome added "an absolute scripted_variables path should produce a contribution-only stage"
              Expect.isTrue added.Value.semanticChanged "adding a global variable is semantic"
              Expect.isTrue (stl.CommitScriptedTypes added.Value) "the add stage should commit"
              Expect.contains (stl.ScriptedVariables()) ("@incremental", "one") "the committed value should be published"

              stl.UpdateFile false variableFile (Some "@incremental = two") |> ignore
              let valueChanged = stl.PrepareScriptedTypes([ relativeFile ], false)
              Expect.isSome valueChanged "the same scripted_variables file should be recognised through a relative path"
              Expect.isTrue valueChanged.Value.semanticChanged "changing a winning value is semantic"
              Expect.isTrue (stl.CommitScriptedTypes valueChanged.Value) "the value stage should commit"
              Expect.contains (stl.ScriptedVariables()) ("@incremental", "two") "the new value should replace the old winner"

              stl.UpdateFile false variableFile (Some "@renamed = two") |> ignore
              let renamed = stl.PrepareScriptedTypes([ variableFile ], false)
              Expect.isSome renamed "renaming a variable should stage"
              Expect.isTrue (stl.CommitScriptedTypes renamed.Value) "the rename stage should commit"
              Expect.isFalse (stl.ScriptedVariables() |> List.exists (fst >> (=) "@incremental")) "rename should remove the old name"
              Expect.contains (stl.ScriptedVariables()) ("@renamed", "two") "rename should publish the new name"

          testWithCapturedLogs "scripted-variable duplicate reorder mirrors full refresh" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let first = Path.GetFullPath(Path.Combine(folder, "common", "scripted_variables", "a_incremental.txt"))
              let second = Path.GetFullPath(Path.Combine(folder, "common", "scripted_variables", "b_incremental.txt"))
              stl.UpdateFile false first (Some "@duplicate = first") |> ignore
              stl.UpdateFile false second (Some "@duplicate = second") |> ignore
              let initial = stl.PrepareScriptedTypes([ first; second ], false)
              Expect.isSome initial "duplicate contributions should stage"
              Expect.isTrue (stl.CommitScriptedTypes initial.Value) "initial duplicate stage should commit"
              let before = stl.ScriptedVariables() |> List.find (fst >> (=) "@duplicate")

              // Swap the two equal-name contributions. The name/value multiset is unchanged,
              // but ordered first-wins semantics select the other value.
              stl.UpdateFile false first (Some "@duplicate = second") |> ignore
              stl.UpdateFile false second (Some "@duplicate = first") |> ignore
              let reordered = stl.PrepareScriptedTypes([ first; second ], false)
              Expect.isSome reordered "reordering duplicate contributions should stage"
              Expect.isTrue reordered.Value.semanticChanged "winner/order changes are semantic even when each value is unchanged"
              Expect.isTrue (stl.CommitScriptedTypes reordered.Value) "the reorder stage should commit"
              let incremental = stl.ScriptedVariables() |> List.find (fst >> (=) "@duplicate")
              Expect.notEqual incremental before "duplicate reorder should change the deterministic winner"
              stl.RefreshCaches()
              Expect.equal
                  incremental
                  (stl.ScriptedVariables() |> List.find (fst >> (=) "@duplicate"))
                  "incremental duplicate winner must exactly match a fresh full model"

          testWithCapturedLogs "contribution stages chain and reject stale resources" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let variableFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_variables", "guard_incremental.txt"))
              let unrelated = Path.GetFullPath(Path.Combine(folder, "events", "guard_incremental.txt"))
              Expect.isNone
                  (stl.PrepareScriptedTypes([ unrelated ], false))
                  "a non-contribution file with no type keys or additional semantic change should not stage"

              stl.UpdateFile false variableFile (Some "@guarded = one") |> ignore
              let first = stl.PrepareScriptedTypes([ variableFile ], false)
              Expect.isSome first "first contribution stage should exist"
              Expect.isTrue (stl.CommitScriptedTypes first.Value) "first chained commit should succeed"
              let noChange = stl.PrepareScriptedTypes([ variableFile ], false)
              Expect.isSome noChange "an unchanged contribution path still has a safe staged index"
              Expect.isFalse noChange.Value.semanticChanged "unchanged contribution should be a semantic no-op"
              Expect.isTrue (stl.CommitScriptedTypes noChange.Value) "no-op chained commit should succeed"

              stl.UpdateFile false variableFile (Some "@guarded = two") |> ignore
              let stale = stl.PrepareScriptedTypes([ variableFile ], false)
              Expect.isSome stale "changed contribution should stage"
              stl.UpdateFile false variableFile (Some "@guarded = three") |> ignore
              Expect.isFalse (stl.CommitScriptedTypes stale.Value) "resource mutation after prepare must reject the stale stage"
              Expect.equal
                  ("@guarded", "one")
                  (stl.ScriptedVariables() |> List.find (fst >> (=) "@guarded"))
                  "a rejected stale stage must not publish its contribution"

              // Deletion has no safe contribution commit API: returning false preserves the
              // caller's existing full model reload fallback instead of mutating staged state.
              Expect.isFalse
                  (stl.RemoveScriptedTypes [ variableFile ])
                  "contribution-only deletion must retain the existing full-refresh fallback"

          testWithCapturedLogs "mixed scripted-variable deletion batch is rejected atomically" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let variableFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_variables", "mixed_delete.txt"))
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              stl.UpdateFile false variableFile (Some "@mixed_delete = present") |> ignore
              let variableStage = stl.PrepareScriptedTypes([ variableFile ], false)
              Expect.isSome variableStage "the scripted-variable contribution should stage before deletion"
              Expect.isTrue (stl.CommitScriptedTypes variableStage.Value) "the scripted-variable contribution should commit"
              let triggerIdsBefore = stl.Types().["scripted_trigger"] |> Array.map _.id

              Expect.isFalse
                  (stl.RemoveScriptedTypes [ triggerFile; variableFile ])
                  "any scripted_variables member must reject the whole mixed deletion batch"
              Expect.isSome
                  (stl.AllEntities() |> Seq.tryFind (fun struct (entity, _) -> entity.filepath = triggerFile))
                  "the scripted type resource must not be partially removed"
              Expect.isSome
                  (stl.AllEntities() |> Seq.tryFind (fun struct (entity, _) -> entity.filepath = variableFile))
                  "the scripted-variable resource must remain for the full-refresh fallback"
              Expect.equal
                  triggerIdsBefore
                  (stl.Types().["scripted_trigger"] |> Array.map _.id)
                  "the mixed-batch rejection must not partially mutate the type index"
              Expect.contains
                  (stl.ScriptedVariables())
                  ("@mixed_delete", "present")
                  "the mixed-batch rejection must not partially mutate contributions"

          testWithCapturedLogs "prepare is pure and commit swaps the type index" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))

              let typesBefore = stl.Types()
              let staged = stl.PrepareScriptedTypes([ triggerFile ], false)
              Expect.isSome staged "prepare should stage a scripted_triggers file"
              Expect.isFalse staged.Value.semanticChanged "unchanged scripted definitions should be a semantic no-op"
              Expect.isNone staged.Value.services "semantic no-op must not allocate replacement global services"
              Expect.isNone staged.Value.lookupSnapshot "semantic no-op must not retain a cloned lookup snapshot"
              Expect.isTrue
                  (System.Object.ReferenceEquals(stl.Types(), typesBefore))
                  "prepare must not reassign the live type index"

              let committed = stl.CommitScriptedTypes staged.Value
              Expect.isTrue committed "commit should succeed when the type index is unchanged since prepare"
              Expect.isFalse
                  (System.Object.ReferenceEquals(stl.Types(), typesBefore))
                  "commit should install the staged type index"
              Expect.contains
                  (stl.Types().["scripted_trigger"] |> Array.map (fun t -> t.id))
                  "test_scripted_trigger_country"
                  "committed type index should still contain the fixture's scripted triggers"

          testWithCapturedLogs "commit is rejected when the type index changed since prepare" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))

              let staged = stl.PrepareScriptedTypes([ triggerFile ], false)
              Expect.isSome staged "prepare should stage a scripted_triggers file"

              // Simulate an external writer replacing lookup.typeDefInfo between prepare and commit.
              stl.RefreshScriptedTypes [ triggerFile ] |> ignore

              let committed = stl.CommitScriptedTypes staged.Value
              Expect.isFalse committed "commit must reject a staged result whose base type index was replaced"

          testWithCapturedLogs "prepare deletion does not mutate live state" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let typesBefore = stl.Types()
              let entitiesBefore = stl.AllEntities() |> Seq.length

              let staged = stl.PrepareFileDeletion([ triggerFile ], true)
              Expect.isSome staged "prepare deletion should produce a stage"
              Expect.equal (stl.Types()) typesBefore "prepare deletion must not mutate live types"
              Expect.equal (stl.AllEntities() |> Seq.length) entitiesBefore "prepare deletion must not remove live entities"

          testWithCapturedLogs "commit file deletion removes file and definitions" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              Expect.contains
                  (stl.Types().["scripted_trigger"] |> Array.map (fun t -> t.id))
                  "test_scripted_trigger_ship"
                  "fixture should contain test_scripted_trigger_ship before deletion"

              let staged = stl.PrepareFileDeletion([ triggerFile ], true)
              Expect.isSome staged "prepare deletion should succeed"
              let committed = stl.CommitFileDeletion staged.Value
              Expect.isTrue committed "commit deletion should succeed"

              let remainingTriggerIds =
                  stl.Types()
                  |> Map.tryFind "scripted_trigger"
                  |> Option.defaultValue [||]
                  |> Array.map (fun t -> t.id)
              Expect.isFalse
                  (remainingTriggerIds |> Array.contains "test_scripted_trigger_ship")
                  "committed deletion must remove definitions defined in the deleted file"

          testWithCapturedLogs "commit file deletion is rejected when resources changed since prepare" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let otherFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))

              let staged = stl.PrepareFileDeletion([ triggerFile ], true)
              Expect.isSome staged "prepare deletion should succeed"

              // Simulate a concurrent edit advancing the resource epoch
              stl.UpdateFile false otherFile (Some "test_scripted_effect = { }") |> ignore

              let committed = stl.CommitFileDeletion staged.Value
              Expect.isFalse committed "commit deletion must reject a stage when resource epoch changed"

          testWithCapturedLogs "commit file deletion is rejected when target file does not exist in resources and leaves state intact" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let typesBefore = stl.Types()
              let entitiesBefore = stl.AllEntities() |> Seq.length
              let nonExistentFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "non_existent.txt"))

              let fakeStage: StagedFileDeletion =
                  { files = [ nonExistentFile ]
                    resourceEpoch = ResourceManagerEager.currentResource ()
                    typeIndex = None
                    scriptedTypes = None }

              let committed = stl.CommitFileDeletion fakeStage
              Expect.isFalse committed "commit deletion must reject a stage with missing target files"
              Expect.equal (stl.Types()) typesBefore "rejected deletion must leave live types unchanged"
              Expect.equal (stl.AllEntities() |> Seq.length) entitiesBefore "rejected deletion must leave live entities unchanged"

          testWithCapturedLogs "commit file deletion is rejected when batch contains both existing and missing files and leaves state intact" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let typesBefore = stl.Types()
              let entitiesBefore = stl.AllEntities() |> Seq.length
              let existingFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let missingFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "missing_other.txt"))

              let fakeStage: StagedFileDeletion =
                  { files = [ existingFile; missingFile ]
                    resourceEpoch = ResourceManagerEager.currentResource ()
                    typeIndex = None
                    scriptedTypes = None }

              let committed = stl.CommitFileDeletion fakeStage
              Expect.isFalse committed "commit deletion must reject a batch when any file is missing"
              Expect.equal (stl.Types()) typesBefore "rejected mixed deletion must leave live types unchanged"
              Expect.equal (stl.AllEntities() |> Seq.length) entitiesBefore "rejected mixed deletion must leave live entities unchanged"
              let stillExists =
                  stl.AllEntities()
                  |> Seq.exists (fun struct (e, _) -> e.filepath = existingFile)
              Expect.isTrue stillExists "existing file in rejected mixed batch must remain in entities"

          testWithCapturedLogs "commit file deletion is rejected when semantic-only guards changed and does not delete resources" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let staged = stl.PrepareFileDeletion([ triggerFile ], true)
              Expect.isSome staged "prepare deletion should succeed"
              Expect.isSome staged.Value.scriptedTypes "staged scripted types should be present"

              // Keep all base identities and resourceEpoch intact, but alter baseOnlyScriptedEffects to simulate a semantic-only guard drift
              let scripted = staged.Value.scriptedTypes.Value
              let driftStage =
                  { staged.Value with
                      scriptedTypes =
                          Some
                              { scripted with
                                  semanticChanged = true
                                  baseOnlyScriptedEffects = box [||] } }

              let committed = stl.CommitFileDeletion driftStage
              Expect.isFalse committed "commit deletion must reject when semantic-only guard fails"

              // Verify that the resource was NOT deleted
              let resourceStillExists =
                  stl.AllEntities()
                  |> Seq.exists (fun struct (e, _) -> e.filepath = triggerFile)
              Expect.isTrue resourceStillExists "semantic-only rejected commit must NOT delete target file resource"

          testWithCapturedLogs "deletion path normalization respects platform case sensitivity on live resources" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let fileLower = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "case_test.txt"))
              let fileUpper = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "CASE_TEST.TXT"))

              let isWindows = System.OperatingSystem.IsWindows()
              if isWindows then
                  // On Windows: updating lowercase file and deleting using uppercase alias must match and delete properly
                  stl.UpdateFile false fileLower (Some "case_test = { }") |> ignore
                  let staged = stl.PrepareFileDeletion([ fileUpper ], true)
                  Expect.isSome staged "prepare deletion using case alias on Windows should succeed"
                  let committed = stl.CommitFileDeletion staged.Value
                  Expect.isTrue committed "committing deletion using case alias on Windows should succeed"

                  let allEntities = stl.AllEntities() |> Seq.map (fun struct (e, _) -> e.filepath.ToLowerInvariant()) |> Seq.toList
                  Expect.isFalse (allEntities |> List.contains (fileLower.ToLowerInvariant())) "resource must be deleted on Windows"
              else
                  // On Unix: fileLower and fileUpper are two distinct files; deleting fileLower must keep fileUpper intact
                  stl.UpdateFile false fileLower (Some "case_test_lower = { }") |> ignore
                  stl.UpdateFile false fileUpper (Some "case_test_upper = { }") |> ignore

                  let staged = stl.PrepareFileDeletion([ fileLower ], true)
                  Expect.isSome staged "prepare deletion for fileLower should succeed"
                  let committed = stl.CommitFileDeletion staged.Value
                  Expect.isTrue committed "committing deletion for fileLower should succeed"

                  let allEntities = stl.AllEntities() |> Seq.map (fun struct (e, _) -> e.filepath) |> Seq.toList
                  Expect.isFalse (allEntities |> List.contains fileLower) "fileLower must be deleted on Unix"
                  Expect.isTrue (allEntities |> List.contains fileUpper) "case-distinct fileUpper must remain intact on Unix"

          testWithCapturedLogs "type-index stage distinguishes range-only and semantic changes" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let index = stl :?> IIncrementalTypeIndex
              let originalText = File.ReadAllText triggerFile

              stl.UpdateFile true triggerFile (Some("\n" + originalText)) |> ignore
              let rangeOnly = index.PrepareTypeIndex [ triggerFile ]
              Expect.isSome rangeOnly "range-only edit should produce an incremental stage"
              Expect.isFalse
                  rangeOnly.Value.semanticChanged
                  "moving unchanged definitions must not dirty validation/completion semantics"

              let renamedText =
                  originalText.Replace(
                      "test_scripted_trigger_ship =",
                      "test_scripted_trigger_ship_renamed =",
                      StringComparison.Ordinal
                  )
              stl.UpdateFile true triggerFile (Some renamedText) |> ignore
              let renamed = index.PrepareTypeIndex [ triggerFile ]
              Expect.isSome renamed "renamed definition should produce an incremental stage"
              Expect.isTrue
                  renamed.Value.semanticChanged
                  "definition identity changes must conservatively dirty global semantics"

          testWithCapturedLogs "scripted stage updates ranges without replacing services" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let originalText = File.ReadAllText triggerFile
              let originalDefinition =
                  stl.Types().["scripted_trigger"]
                  |> Array.find (fun definition -> definition.id = "test_scripted_trigger_ship")

              stl.UpdateFile true triggerFile (Some("\n" + originalText)) |> ignore
              let staged = stl.PrepareScriptedTypes([ triggerFile ], false)
              Expect.isSome staged "range-only scripted edit should produce a stage"
              Expect.isFalse staged.Value.semanticChanged "range-only edit must retain live semantic services"
              Expect.isNone staged.Value.services "range-only stage must omit replacement services"
              Expect.isTrue (stl.CommitScriptedTypes staged.Value) "range-only stage should commit"

              let updatedDefinition =
                  stl.Types().["scripted_trigger"]
                  |> Array.find (fun definition -> definition.id = "test_scripted_trigger_ship")
              Expect.equal
                  updatedDefinition.range.StartLine
                  (originalDefinition.range.StartLine + 1)
                  "range-only commit must update navigation positions"

          testWithCapturedLogs "scripted definition changes alter the semantic signature" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let provider = stl :?> ISemanticDeltaProvider
              let originalText = File.ReadAllText triggerFile
              let originalSignature = provider.SemanticSignatureForFile triggerFile
              Expect.isSome originalSignature "scripted trigger should expose a semantic signature"

              let changedDefinitionText =
                  originalText.Replace(
                      "test_scripted_trigger_ship =",
                      "test_scripted_trigger_ship_changed =",
                      StringComparison.Ordinal
                  )
              stl.UpdateFile true triggerFile (Some changedDefinitionText) |> ignore
              Expect.notEqual
                  (provider.SemanticSignatureForFile triggerFile)
                  originalSignature
                  "scripted definition changes must not take the semantic no-op path"
              let staged = stl.PrepareScriptedTypes([ triggerFile ], true)
              Expect.isSome staged "semantic scripted change should produce a stage"
              Expect.isTrue staged.Value.semanticChanged "additional semantic delta must force a semantic stage"
              Expect.isSome staged.Value.services "semantic stage must contain replacement services"

          testWithCapturedLogs "semantic signature ignores ranges but tracks cross-file definitions" <| fun () ->
              let folder = "./testfiles/localisationtests/gamefiles"
              let configPath = "./testfiles/localisationtests/test.cwt"
              let settings = emptyStellarisSettings folder
              let settings =
                  { settings with
                      rules =
                          Some
                              { ruleFiles = [ configPath, File.ReadAllText configPath ]
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }
              let stl = STLGame(settings) :> IGame<STLComputedData>
              let provider = stl :?> ISemanticDeltaProvider
              let eventFile =
                  stl.AllEntities()
                  |> Seq.map (fun struct (entity, _) -> entity.filepath)
                  |> Seq.find (fun filepath -> filepath.EndsWith("test_events.txt"))
              let originalText = File.ReadAllText eventFile
              let originalSignature = provider.SemanticSignatureForFile eventFile
              Expect.isSome originalSignature "loaded event should expose a semantic signature"

              stl.UpdateFile true eventFile (Some(Environment.NewLine + originalText)) |> ignore
              Expect.equal
                  (provider.SemanticSignatureForFile eventFile)
                  originalSignature
                  "range-only movement must not dirty the semantic contribution"

              let renamedText = originalText.Replace("defined_event", "renamed_event", StringComparison.Ordinal)
              stl.UpdateFile true eventFile (Some renamedText) |> ignore
              Expect.notEqual
                  (provider.SemanticSignatureForFile eventFile)
                  originalSignature
                  "changing a saved event target must dirty global validation semantics"

          testWithCapturedLogs "cancellable file validation returns no partial result" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let triggerFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_triggers", "test.txt"))
              let cancellable = stl :?> ICancellableFileValidation

              let cancelled =
                  cancellable.ValidateFileCancellable(false, triggerFile, (fun () -> true))
              Expect.isNone cancelled "an already superseded snapshot must stop before validation"

              let cancelledBatch =
                  stl.ValidateFilesLocalCancellable([ triggerFile ], (fun () -> true))
              Expect.isNone cancelledBatch "an already superseded local batch must stop before validation"

              let mutable cancellationChecks = 0
              let cancelledDuringValidation =
                  cancellable.ValidateFileCancellable(
                      false,
                      triggerFile,
                      (fun () ->
                          cancellationChecks <- cancellationChecks + 1
                          cancellationChecks > 3)
                  )
              Expect.isGreaterThan cancellationChecks 3 "validation should sample cancellation within rule work"
              Expect.isNone cancelledDuringValidation "a mid-validation cancellation must discard partial diagnostics"

              let completed =
                  cancellable.ValidateFileCancellable(false, triggerFile, (fun () -> false))
              Expect.isSome completed "the same cancellable path must preserve normal validation results"

              let completedBatch =
                  stl.ValidateFilesLocalCancellable([ triggerFile ], (fun () -> false))
              Expect.isSome completedBatch "the local batch path must preserve normal validation results"

              let forced =
                  stl.ForceDynamicParameterDataForFiles [ triggerFile; triggerFile; triggerFile + ".missing" ]
              Expect.equal forced 1 "targeted prewarm should force each loaded file at most once"

          testWithCapturedLogs "detached overlay resolves definitions across candidate files" <| fun () ->
              let stl, folder = stlScriptedGame ()
              let effectFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let eventFile = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let liveTypesBefore = stl.Types()
              let liveEffectsBefore = stl.ScriptedEffects() |> List.map (fun effect -> effect.Name.GetString())
              let definition = "overlay_effect = { set_country_flag = yes }"
              let reference name =
                  $"namespace = overlay\ncountry_event = {{ is_triggered_only = yes option = {{ {name} = yes }} }}"
              let unresolved errors =
                  errors
                  |> List.filter (fun error -> error.message.Contains("overlay_effect", StringComparison.Ordinal))

              let isolatedReferenceErrors = stl.ValidateOverlayFile(eventFile, reference "overlay_effect")
              Expect.isNonEmpty
                  (unresolved isolatedReferenceErrors)
                  "the live single-file service must not know the detached definition"

              let resolved =
                  stl.ValidateOverlayFilesCancellable(
                      [ effectFile, definition; eventFile, reference "overlay_effect" ],
                      (fun () -> false))
              Expect.isSome resolved "the detached batch should complete"
              Expect.isEmpty
                  (unresolved resolved.Value)
                  $"a sibling overlay definition must be visible to its reference: %A{resolved.Value |> List.map _.message}"

              let missing =
                  stl.ValidateOverlayFilesCancellable(
                      [ effectFile, definition; eventFile, reference "missing_overlay_effect" ],
                      (fun () -> false))
              Expect.isSome missing "the unresolved detached batch should complete"
              Expect.isNonEmpty
                  (missing.Value |> List.filter (fun error -> error.message.Contains("missing_overlay_effect", StringComparison.Ordinal)))
                  "an absent sibling definition must remain unresolved"

              let cancelled =
                  stl.ValidateOverlayFilesCancellable(
                      [ effectFile, definition; eventFile, reference "overlay_effect" ],
                      (fun () -> true))
              Expect.isNone cancelled "an already cancelled detached batch must publish no partial result"
              Expect.equal (stl.Types()) liveTypesBefore "detached types must never commit to the live lookup"
              Expect.equal
                  (stl.ScriptedEffects() |> List.map (fun effect -> effect.Name.GetString()))
                  liveEffectsBefore
                  "detached scripted effects must never commit to the live lookup"

          testWithCapturedLogs "detached overlay resolves localisation keys across candidate files" <| fun () ->
              // Two languages so the default-language key set is validated for the
              // non-default overlay language, matching CWTools' per-language rules.
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripted"
              let configtext = configFilesFromDir folder
              let settings =
                  { emptyStellarisSettings folder with
                      validation = { validateVanilla = false; experimental = true; langs = [| STL STLLang.English; STL STLLang.Chinese |] }
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }
              let stl = STLGame(settings) :> IGame<STLComputedData>
              let locFileEn = Path.GetFullPath(Path.Combine(folder, "localisation", "english", "overlay_l_english.yml"))
              let locFileZh = Path.GetFullPath(Path.Combine(folder, "localisation", "simp_chinese", "overlay_l_simp_chinese.yml"))
              let eventFile = Path.GetFullPath(Path.Combine(folder, "events", "overlay_loc.txt"))
              let liveLocBefore = stl.AllLoadedLocalisation()
              Expect.isTrue
                  (liveLocBefore |> List.exists (fun entry -> entry.Contains("base_l_simp_chinese.yml", StringComparison.Ordinal)))
                  (sprintf "fixture localisation must load: %A" (liveLocBefore |> List.truncate 20))
              let locEn = "l_english:\n overlay_loc_1_title:0 \"Overlay Title\"\n"
              let locZh = "l_simp_chinese:\n overlay_loc_1_title:0 \"Overlay Title\"\n"
              let event = "namespace = overlay\ncountry_event = { id = overlay_loc_1 is_triggered_only = yes }\n"
              let eventWithoutId = "namespace = overlay\ncountry_event = { is_triggered_only = yes }\n"
              let eventFileWithoutId = Path.GetFullPath(Path.Combine(folder, "events", "overlay_loc_noid.txt"))
              let missingOnly = stl.ValidateOverlayFilesCancellable([ eventFile, event; eventFileWithoutId, eventWithoutId ], (fun () -> false))
              Expect.isSome missingOnly "the missing-key batch should complete"
              Expect.isNonEmpty
                  (missingOnly.Value |> List.filter (fun error -> error.message.Contains("overlay_loc_1_title", StringComparison.Ordinal) || error.message.Contains("_title", StringComparison.Ordinal)))
                  (sprintf "detached type localisation must flag missing required keys: %A" (missingOnly.Value |> List.map (fun e -> e.code + " " + e.message + " @ " + e.range.FileName)))
              let resolved = stl.ValidateOverlayFilesCancellable([ locFileEn, locEn; locFileZh, locZh; eventFile, event ], (fun () -> false))
              Expect.isSome resolved "the localisation batch should complete"
              Expect.isEmpty
                  (resolved.Value |> List.filter (fun error -> error.message.Contains("overlay_loc_1_title", StringComparison.Ordinal)))
                  (sprintf "sibling overlay localisation keys must satisfy the required event title: %A" (resolved.Value |> List.map _.message))
              Expect.equal (stl.AllLoadedLocalisation()) liveLocBefore "overlay localisation must never enter the live catalog"

              let mutable completedCancellationChecks = 0
              let completedForCancellationCount =
                  stl.ValidateOverlayFilesCancellable(
                      [ locFileEn, locEn; locFileZh, locZh; eventFile, event ],
                      (fun () ->
                          completedCancellationChecks <- completedCancellationChecks + 1
                          false))
              Expect.isSome completedForCancellationCount "the cancellation-count baseline must complete"

              let mutable lateCancellationChecks = 0
              let cancelledAfterGlobalLocalisation =
                  stl.ValidateOverlayFilesCancellable(
                      [ locFileEn, locEn; locFileZh, locZh; eventFile, event ],
                      (fun () ->
                          lateCancellationChecks <- lateCancellationChecks + 1
                          lateCancellationChecks >= completedCancellationChecks))
              Expect.isNone
                  cancelledAfterGlobalLocalisation
                  "cancellation after global localisation must discard the completed diagnostics"

              let cancelled = stl.ValidateOverlayFilesCancellable([ locFileEn, locEn; eventFile, event ], (fun () -> true))
              Expect.isNone cancelled "an already cancelled localisation batch must publish no partial result"

          testWithCapturedLogs "commit refreshes scripted parameter enums" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripteddefaults"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let effectFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let eventFile = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))
              let updatedEffects =
                  File.ReadAllText(effectFile)
                  + "\nscripted_effect_incremental_param = { set_country_flag = $incremental_param$ }\n"

              stl.UpdateFile false effectFile (Some updatedEffects) |> ignore

              let staged = stl.PrepareScriptedTypes([ effectFile ], false)
              Expect.isSome staged "prepare should stage a scripted effect parameter change"
              Expect.isTrue staged.Value.semanticChanged "dynamic parameter additions must be semantic changes"
              Expect.isSome staged.Value.services "semantic changes must stage replacement services"
              let stagedEnums =
                  staged.Value.newEnumDefs
                  :?> Map<string, string * (string * range option) array>
              let stagedParams =
                  stagedEnums.["scripted_effect_params"]
                  |> snd
                  |> Array.map fst
              Expect.contains
                  stagedParams
                  "incremental_param"
                  "the staged enum should contain the newly parsed parameter"
              Expect.isTrue
                  (stl.CommitScriptedTypes staged.Value)
                  "commit should install the updated scripted parameter enum"
              Expect.contains
                  (stl.Types().["scripted_effect"] |> Array.map (fun definition -> definition.id))
                  "scripted_effect_incremental_param"
                  "semantic commit must install the staged type index as well as services"
              Expect.contains
                  (stl.ScriptedEffects() |> List.map (fun effect -> effect.Name.GetString()))
                  "scripted_effect_incremental_param"
                  "incremental update must publish the refreshed scripted effect links"

              let eventText =
                  """
namespace = incremental_param

country_event = {
    is_triggered_only = yes
    option = {
        scripted_effect_incremental_param = {
            incremental_param = yes
        }
    }
}
"""

              let errors = stl.UpdateFile false eventFile (Some eventText)
              let parameterErrors =
                  errors
                  |> List.filter (fun error ->
                      error.message.Contains("incremental_param", StringComparison.Ordinal)
                      || error.message.Contains("scripted_effect_params", StringComparison.Ordinal))

              Expect.isEmpty
                  parameterErrors
                  $"incremental commit should validate the new scripted parameter without a full refresh: %A{parameterErrors |> List.map _.message}"

              let incrementalDiagnostics =
                  errors
                  |> List.map (fun error -> error.code, error.severity, error.message)
                  |> List.distinct
                  |> List.sort
              let effectSemantics effects =
                  effects
                  |> List.map (fun (effect: Effect) ->
                      effect.Name.GetString(), effect.Type, (effect.Scopes |> List.map _.Tag))
                  |> List.sort
              let incrementalEffects = effectSemantics (stl.ScriptedEffects())
              stl.RefreshCaches()
              let fullDiagnostics =
                  stl.ValidateFile false eventFile
                  |> List.map (fun error -> error.code, error.severity, error.message)
                  |> List.distinct
                  |> List.sort
              Expect.equal
                  incrementalDiagnostics
                  fullDiagnostics
                  "incremental scripted diagnostics must match a full refresh"
              Expect.equal
                  incrementalEffects
                  (effectSemantics (stl.ScriptedEffects()))
                  "incremental scripted effects must match a full refresh"

              stl.UpdateFile false effectFile (Some(File.ReadAllText effectFile)) |> ignore
              let removal = stl.PrepareScriptedTypes([ effectFile ], false)
              Expect.isSome removal "prepare should stage scripted parameter removal"
              let removalEnums =
                  removal.Value.newEnumDefs
                  :?> Map<string, string * (string * range option) array>
              let removalParams =
                  removalEnums.["scripted_effect_params"]
                  |> snd
                  |> Array.map fst
              Expect.isFalse
                  (removalParams |> Array.contains "incremental_param")
                  "the staged enum should remove parameters no longer present in resources"
              Expect.isTrue
                  (stl.CommitScriptedTypes removal.Value)
                  "commit should install the enum after a scripted parameter is removed"

          testWithCapturedLogs "snapshot refreshes per file after definition edits" <| fun () ->
              let folder = "./testfiles/configtests/ruleswithglobaltests/STL/scripteddefaults"
              let configtext = configFilesFromDir folder

              let settings =
                  { emptyStellarisSettings folder with
                      rules =
                          Some
                              { ruleFiles = configtext
                                validateRules = true
                                debugRulesOnly = false
                                debugMode = false } }

              let stl = STLGame(settings) :> IGame<STLComputedData>
              let effectFile = Path.GetFullPath(Path.Combine(folder, "common", "scripted_effects", "test.txt"))
              let eventFile = Path.GetFullPath(Path.Combine(folder, "events", "test.txt"))

              let callSiteErrors (errors: CWError list) =
                  errors
                  |> List.filter (fun e ->
                      e.message.StartsWith("This call of scripted effect", StringComparison.Ordinal)
                      && e.message.Contains("scripted_effect_default_param_validation"))

              // First pass builds the whole-workspace snapshot; the definition expands cleanly.
              let baseline =
                  stl.ValidateFilesLocalCancellable([ eventFile ], (fun () -> false))
                  |> Option.defaultValue []
              Expect.isEmpty (callSiteErrors baseline) "baseline definition must expand cleanly"

              // Break the definition body; the call site in the event file is unchanged.
              let brokenDefinition =
                  (File.ReadAllText effectFile).Replace(
                      "set_country_flag = $dynamic|no$",
                      "set_country_flag = @undefined_var",
                      System.StringComparison.Ordinal
                  )
              Expect.isTrue
                  (brokenDefinition.Contains("set_country_flag = @undefined_var"))
                  "broken definition text must be staged"
              stl.UpdateFile false effectFile (Some brokenDefinition) |> ignore
              let staged = stl.PrepareScriptedTypes([ effectFile ], false)
              Expect.isSome staged "prepare should stage the broken definition"
              Expect.isTrue (stl.CommitScriptedTypes staged.Value) "commit should publish the broken definition"

              // Only the definition file changed; the snapshot must pick up the new
              // body for the already-referenced call site.
              let afterBreak =
                  stl.ValidateFilesLocalCancellable([ eventFile ], (fun () -> false))
                  |> Option.defaultValue []
              Expect.isNonEmpty
                  (callSiteErrors afterBreak)
                  "a refreshed snapshot must surface call-site expansion errors for edited definitions"

              // Removing the definition removes its entries from the snapshot; the
              // stale call site must no longer produce expansion errors.
              stl.UpdateFile false effectFile (Some "") |> ignore
              let removalStaged = stl.PrepareScriptedTypes([ effectFile ], false)
              Expect.isSome removalStaged "prepare should stage the definition removal"
              Expect.isTrue (stl.CommitScriptedTypes removalStaged.Value) "commit should publish the removal"
              let afterRemoval =
                  stl.ValidateFilesLocalCancellable([ eventFile ], (fun () -> false))
                  |> Option.defaultValue []
              Expect.isEmpty
                  (callSiteErrors afterRemoval)
                  "removing a definition must invalidate its snapshot entries" ]

[<Tests>]
let irSubfolderTests =
    testList "validation ir" (testSubdirectories 0 true "./testfiles/configtests/rulestests/IR" |> List.ofSeq)

[<Tests>]
let hoi4SubfolderTests =
    testList
        "validation hoi4"
        (testSubdirectories 3 true "./testfiles/configtests/rulestests/HOI4"
         |> List.ofSeq)

[<Tests>]
let vic3SubfolderTests =
    testList
        "validation vic3"
        (testSubdirectories 2 true "./testfiles/configtests/rulestests/VIC3"
         |> List.ofSeq)

[<Tests>]
let specialtests =
    // testList
    // "log"
    testCase "log modifiers"
    <| fun () ->
        let configtext =
            [ ("./testfiles/scriptedorstatictest/setup.log",
               File.ReadAllText "./testfiles/scriptedorstatictest/setup.log") ]

        let modfile =
            SetupLogParser.parseLogsFile "./testfiles/scriptedorstatictest/setup.log"
        // (modfile |> (function |Failure(e, _,_) -> eprintfn "%s" e |_ -> ()))
        let modifiers =
            (modfile
             |> (function
             | ParserResult.Success(p, _, _) -> SetupLogParser.processLogs p
             | ParserResult.Failure _ -> failwith "todo"))

        // modifierCategoryManager is a process-global singleton that other tests
        // re-initialise under parallelism; pin it to the Stellaris defaults so the
        // assertions below are deterministic.
        UtilityParser.initializeModifierCategories None (Some(defaultModifiersInputs ()))
        let settings = emptyStellarisSettings "./testfiles/scriptedorstatictest"
        // UtilityParser.initializeScopes None (Some defaultScopeInputs)
        let stl =
            STLGame(
                { settings with
                    rules =
                        Some
                            { ruleFiles = configtext
                              validateRules = false
                              debugRulesOnly = false
                              debugMode = false }
                    embedded =
                        ManualSettings
                            { emptyEmbeddedSettings with
                                modifiers = modifiers |> List.toArray } }
            )
            :> IGame<STLComputedData>
        // let stl = STLGame("./testfiles/scriptedorstatictest/", FilesScope.All, "", [], [], modifiers, [], [], [STL STLLang.English], false, true, false)
        let exp =
            [| { tag = "test"
                 categories = [ modifierCategoryManager.ParseModifier () "pop" ] } |]

        Expect.equal (stl.StaticModifiers()) exp ""
