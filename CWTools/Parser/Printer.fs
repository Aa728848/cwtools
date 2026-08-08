namespace CWTools.Parser

open Types
open FParsec

module CKPrinter =
    let private tabs n = String.replicate n "\t"

    let private printTroop depth t = (tabs depth) + t.ToString() + "\n"

    let private printValuelist depth is =
        let printOne = (fun i -> tabs depth + (string i) + "\n")
        List.map printOne is |> List.fold (+) ""


    let rec private printValue (sb: System.Text.StringBuilder) v depth =
        match v with
        | Clause kvl ->
            sb.Append("{\n") |> ignore
            printKeyValueList sb kvl (depth + 1) |> ignore
            sb.Append(tabs depth).Append("}") |> ignore
        | x -> sb.Append(x.ToString()) |> ignore

    and private printKeyValue (sb: System.Text.StringBuilder, leadingNewline, prevStart, prevEnd) kv depth =
        match kv with
        | CommentStatement({ Position = r; Comment = c }) ->
            if not (r.StartLine = prevStart && r.StartLine = prevEnd || (not leadingNewline)) then
                sb.Append("\n") |> ignore
            sb.Append(tabs depth).Append("#").Append(c) |> ignore
            sb, true, r.StartLine, r.EndLine
        | KeyValue(PosKeyValue(r, KeyValueItem(key, v, op))) ->
            if leadingNewline then
                sb.Append("\n") |> ignore
            sb.Append(tabs depth).Append(key).Append(" ").Append(operatorToString op).Append(" ") |> ignore
            printValue sb v depth
            sb, true, r.StartLine, r.EndLine
        | Value(r, v) ->
            if leadingNewline then
                sb.Append("\n") |> ignore
            sb.Append(tabs depth) |> ignore
            printValue sb v depth
            sb, true, r.StartLine, r.EndLine

    and private printKeyValueList (sb: System.Text.StringBuilder) kvl depth : string =
        let sb, leadingNewline, _, _ =
            kvl
            |> List.fold (fun acc kv -> printKeyValue acc kv depth) (sb, false, -1, -1)
        if leadingNewline then
            sb.Append("\n") |> ignore
        sb.ToString()

    let printTopLevelKeyValueList kvl =
        let sb, _, _, _ =
            kvl
            |> List.fold
                (fun acc kv ->
                    match kv with
                    | KeyValue(PosKeyValue(_, KeyValueItem(_, Clause _, _))) as x ->
                        let res, a, b, c = printKeyValue acc kv 0
                        res.Append("\n") |> ignore
                        res, a, b, c
                    | x -> printKeyValue acc kv 0)
                (System.Text.StringBuilder(), false, -1, -1)
        sb.ToString()
    // |> (fun (res, leadingNewline, _, _) -> if leadingNewline then res + "\n" else res)

    // kvl |> List.map (
    //     function
    //     | KeyValue (PosKeyValue(_, KeyValueItem(_, Clause _, _))) as x -> printKeyValue x 0, true
    //     | x -> printKeyValue x 0, false
    // ) |> List.fold (fun (acc, start) (nextString, newline) -> if newline && (not start) then acc + nextString + "\n", false else acc + nextString, false) ("", true)
    // |> fst
    let private prettyPrint ef =
        let (ParsedFile sl) = ef
        printKeyValueList (System.Text.StringBuilder()) sl 0

    let private prettyPrintResult =
        function
        | Success(v, _, _) ->
            let (ParsedFile ev) = v
            printKeyValueList (System.Text.StringBuilder()) ev 0
        | Failure(msg, _, _) -> msg

    let api =
        { prettyPrintFile = prettyPrint
          prettyPrintStatements = (fun f -> printKeyValueList (System.Text.StringBuilder()) f 0)
          prettyPrintStatement = (fun f -> printKeyValueList (System.Text.StringBuilder()) [ f ] 0)
          prettyPrintFileResult = prettyPrintResult }