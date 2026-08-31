namespace CWTools.Rules

module RulesCache =
    // Binary serialization of in-memory StringTokens has been permanently retired.
    // CWT rules, docs and modifiers are parsed directly from text sources in < 1s,
    // ensuring consistent intern token mappings and zero cross-process scope drift.
    let mutable globalRulesCacheDir: string option = None
