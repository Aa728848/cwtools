namespace CWTools.Rules

open System

module RulesParserConstants =
    [<Literal>]
    let IntFieldDefaultMinimum = -92_000_000_000_000L

    [<Literal>]
    let IntFieldDefaultMaximum = 92_000_000_000_000L

    [<Literal>]
    let CardinalityDefaultMaximum = 10000

    [<Literal>]
    let floatFieldDefaultMinimum = -9E+18M

    [<Literal>]
    let floatFieldDefaultMaximum = 9E+18M
