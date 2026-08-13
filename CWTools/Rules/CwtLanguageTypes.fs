namespace CWTools.CwtLanguage

open CWTools.Common
open CWTools.Utilities.Position

/// Analysis phases for CWT diagnostics (handoff doc §5). The phase orders
/// pipeline behaviour: Syntax/Structure run per keystroke, Project and
/// Activation only on complete snapshots.
type CwtDiagnosticPhase =
    | Syntax
    | Structure
    | Expression
    | Project
    | Activation

/// Symbol kinds declared by CWT files (handoff doc §5).
type CwtSymbolKind =
    | CwtType
    | CwtSubtype
    | CwtEnum
    | CwtComplexEnum
    | CwtValueSet
    | CwtAlias
    | CwtSingleAlias
    | CwtScope
    | CwtScopeGroup
    | CwtLink
    | CwtModifierCategory

/// A declaration in a CWT document. `name` is the bare symbol name without
/// the declaration prefix (e.g. `planet_class` for `type[planet_class]`).
type CwtSymbol =
    { kind: CwtSymbolKind
      name: string
      range: range
      filePath: string }

/// A single CWT document diagnostic. `code` uses the CWT0xx families
/// (docs/diagnostic-codes.md); `messageKey` is a stable key resolved to
/// English/Chinese at the localization boundary (server side), and
/// `messageArgs` fills its placeholders.
type CwtDiagnostic =
    { code: string
      severity: Severity
      messageKey: string
      messageArgs: string list
      range: range
      phase: CwtDiagnosticPhase
      related: (string * range) list }

/// A completion candidate produced by the CWT language service. `kind` is a
/// stable category name mapped to LSP CompletionItemKind in src/Main.
type CwtCompletionItem =
    { label: string
      kind: string
      detail: string option
      documentation: string option
      insertText: string option }

/// Single-file analysis result. `document` is present when the file parsed;
/// `canContributeToProjectIndex` is false when a structural error prevents a
/// trustworthy model; `canActivateRules` is reserved for Phase 4.
type CwtAnalysisResult =
    { document: CwtDocumentModel option
      diagnostics: CwtDiagnostic list
      canContributeToProjectIndex: bool
      canActivateRules: bool }

/// A symbol reference inside a document: `enum[x]`, `scope[x]`,
/// `scope_group[x]`, `value_set[x]`, `event_target[x]`, `<type>`.
/// Declaration keys are definitions, not references.
and CwtReference =
    { kind: CwtSymbolKind
      name: string
      range: range
      filePath: string }

and CwtDocumentModel =
    { filePath: string
      symbols: CwtSymbol list
      rootBlockNames: string list
      /// Symbol references extracted from the document (Phase 3).
      references: CwtReference list
      /// `## inject` targets: (sourcePath, memberPath, range).
      injects: (string * string * range) list }
