namespace CWTools.Rules

open System

module RulesParserConstants =
    [<Literal>]
    let IntFieldDefaultMinimum = Int32.MinValue

    [<Literal>]
    let IntFieldDefaultMaximum = Int32.MaxValue

    [<Literal>]
    let CardinalityDefaultMaximum = 10000

    [<Literal>]
    let floatFieldDefaultMinimum = -9E+18M

    [<Literal>]
    let floatFieldDefaultMaximum = 9E+18M
