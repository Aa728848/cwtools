namespace Reporters

open Chiron.Builder
open Chiron
open CWToolsCLI.Validator
open Pastel
open System.Drawing
open System.IO
open System.Text
open System


type Reporter =
    | CLI
    | CSV
    | JSON

module Reporters =

    let ne = Environment.NewLine

    let private csvEscape (value: string) =
        "\"" + value.Replace("\"", "\"\"") + "\""

    let private formatPosition (position: CWTools.Utilities.Position.range) =
        sprintf "%s:%i:%i" position.FileName position.StartLine position.StartColumn

    let cliReporter outputFile (errors: ValidationViewModelRow list) =
        let grouped =
            errors
            |> List.groupBy (fun e ->
                match e with
                | ValidationViewModelRow.Parse r -> "CW001", "Error", r.message
                | ValidationViewModelRow.Error r -> r.category, r.severity.ToString(), r.message)
            |> List.sortBy (fun ((category, severity, message), _) -> category, severity, message)

        let sb = new StringBuilder()

        let appendIndented indent (value: string) =
            value.Replace("\r\n", "\n").Split('\n')
            |> Array.iter (fun line -> sb.AppendLine(String.replicate indent " " + line) |> ignore)

        let locationKey row =
            match row with
            | ValidationViewModelRow.Parse r -> r.file, 0, 0
            | ValidationViewModelRow.Error r -> r.position.FileName, r.position.StartLine, r.position.StartColumn

        let printGroup ((category, severity, message), errorList: ValidationViewModelRow list) =
            let suffix = if errorList.Length = 1 then "occurrence" else "occurrences"
            sb.AppendLine(sprintf "%s [%s] - %i %s" category severity errorList.Length suffix) |> ignore
            appendIndented 2 message

            errorList
            |> List.sortBy locationKey
            |> List.iter (fun row ->
                match row with
                | ValidationViewModelRow.Parse r -> sb.AppendLine(sprintf "  - %s" r.file) |> ignore
                | ValidationViewModelRow.Error r ->
                    sb.AppendLine(sprintf "  - %s" (formatPosition r.position)) |> ignore

                    r.related
                    |> List.iter (fun related ->
                        sb.AppendLine(
                            sprintf "      related: %s - %s" (formatPosition related.position) related.message
                        )
                        |> ignore))

            sb.AppendLine() |> ignore

        sb.AppendLine(sprintf "%i diagnostics in %i groups" errors.Length grouped.Length) |> ignore
        sb.AppendLine() |> ignore
        grouped |> List.iter printGroup

        match outputFile with
        | Some file -> File.WriteAllText(file, sb.ToString())
        | None -> printf "%s" (sb.ToString().Pastel(Color.Red))


    let csvReporter outputFile (errors: ValidationViewModelRow list) =
        let result =
            let sb = new StringBuilder()
            sb.Append("file,line,severity,code,message") |> ignore

            errors
            |> List.iter (fun e ->
                e
                |> function
                    | ValidationViewModelRow.Parse(r) ->
                        sb.Append(
                            sprintf "%s%s,%s,%s,%s,\"%s\"" ne r.file "0" "error" "CW001" (r.message.Replace(ne, ""))
                        )
                        |> ignore
                    | Error(r) ->
                        sb.Append(
                            sprintf
                                "%s%s,%s,%s,%s,%s"
                                ne
                                r.position.FileName
                                (r.position.StartLine.ToString())
                                (r.severity.ToString())
                                r.category
                                (csvEscape
                                    (String.concat
                                        " | "
                                        (r.message
                                         :: (r.related
                                             |> List.map (fun related ->
                                                 sprintf
                                                     "related %s: %s"
                                                     (related.position.ToShortString())
                                                     related.message)))))
                        )
                        |> ignore)

            sb.ToString()
        // List.fold (fun s e -> e |> function |ValidationViewModelRow.Parse(r) -> s + ne + r.file + ",\"" + r.error.Replace(System.Environment.NewLine,"") + "\"" |Error(r) -> s + ne + r.position + "," + r.error.Replace(ne, "")) "file,error" errors
        match outputFile with
        | Some file -> File.WriteAllText(file, result)
        | None -> printf "%s" result

    type GroupedValdationViewModelRows =
        { file: string
          errors: ValidationViewModelRow list }

    type GroupedValdationViewModelRows with
        static member ToJson(g: GroupedValdationViewModelRows) =
            json {
                do! Json.write "file" g.file
                do! Json.write "errors" g.errors
            }

    type JsonErrorReport =
        { errors: GroupedValdationViewModelRows list
          errorCount: int
          supressedErrorCount: int
          rootDirectory: string }

    type JsonErrorReport with
        static member ToJson(jer: JsonErrorReport) =
            json {
                do! Json.write "errorCount" jer.errorCount
                do! Json.write "supressedErrorCount" jer.supressedErrorCount
                do! Json.write "files" jer.errors
                do! Json.write "rootDirectory" jer.rootDirectory
            }

    let jsonReporter
        rootDirectory
        outputFile
        (errors: ValidationViewModelRow list)
        (supressedErrors: ValidationViewModelRow list)
        =
        let grouped =
            errors
            |> List.groupBy (fun e ->
                e
                |> function
                    | ValidationViewModelRow.Parse(r) -> r.file
                    | ValidationViewModelRow.Error(e) -> e.position.FileName)
            |> List.map (fun (k, v) -> { file = k; errors = v })
            |> List.sortBy (fun r -> r.file)

        let jsonErrorReport =
            { errors = grouped
              errorCount = errors.Length
              supressedErrorCount = supressedErrors.Length
              rootDirectory = rootDirectory }

        let outputText = jsonErrorReport |> Json.serialize |> Json.format

        match outputFile with
        | Some file -> File.WriteAllText(file, outputText)
        | None -> printf "%s" outputText
