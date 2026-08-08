namespace CWTools.Parser

open FParsec
open Types


module CKParser =

    let parseEventFile filepath =
        runParserOnFile SharedParsers.alle () filepath (System.Text.Encoding.GetEncoding(1252))

    let private applyParser (parser: Parser<'Result, 'UserState>) (stream: CharStream<'UserState>) =
        let reply = parser stream

        if reply.Status = Ok then
            Success(reply.Result, stream.UserState, stream.Position)
        else
            let error = ParserError(stream.Position, stream.UserState, reply.Error)
            Failure(error.ToString(stream), error, stream.UserState)

    let parseFile (filepath: string) =
        use stream = new CharStream<unit>(filepath, System.Text.Encoding.GetEncoding(1252))
        stream.UserState <- ()
        stream.Name <- filepath
        applyParser SharedParsers.all stream


    let parseString fileString filename =
        runParserOnString SharedParsers.all () filename fileString

    let getSuccess result =
        match result with
        | Success(s, _, _) -> s
        | _ -> ParsedFile []
