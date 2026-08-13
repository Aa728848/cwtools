namespace CWTools.CwtLanguage

/// Candidate-rule activation state machine (handoff doc §4.6). Pure logic —
/// the actual game-model swap happens under the game-state write lock in
/// src/Main. Three states must never collapse into one boolean:
///
/// - the candidate file set can be parsed (snapshot has documents);
/// - the candidate set can produce a usable rules model (no blocking errors);
/// - the candidate has become the active model (activation committed).
module CwtActivation =

    /// Rules generation/content identity of the active game model.
    type CwtActiveRules =
        { generation: int
          contentHash: string }

    type CwtActivationDecision =
        /// Candidate is valid, differs from active rules, and may be swapped.
        | Activate
        /// Candidate is unusable; the active model is kept (last-known-good).
        | Rejected of reason: string
        /// Nothing to do (candidate identical to active, or no candidate).
        | NoChange

    /// Stable, deterministic content hash over the ordered rule file list
    /// (normalised paths + text). FNV-1a 64-bit, hex-encoded.
    let contentHash (files: (string * string) list) : string =
        let mutable hash = 1469598103934665603UL
        for (filePath, text) in files |> List.sortBy (fun (p, _) -> CwtProjectIndex.normalizePath p) do
            for b in System.Text.Encoding.UTF8.GetBytes(CwtProjectIndex.normalizePath filePath + "\u0000" + text) do
                hash <- hash ^^^ uint64 b
                hash <- hash * 1099511628211UL
        hash.ToString("x16")

    /// Blocking diagnostic codes: presence of any of these in the candidate
    /// snapshot prevents activation. Defaults to the Error-level set
    /// (syntax, malformed expressions, ambiguous models).
    let defaultBlockingCodes =
        set [ "CWT001"; "CWT201"; "CWT113"; "CWT302"; "CWT401" ]

    /// True when every parsed document carries no blocking diagnostic and no
    /// file failed to parse (parse failures produce no document and mean the
    /// candidate rules model would be incomplete).
    let candidateIsUsable (snapshot: CwtProjectSnapshot) (blockingCodes: Set<string>) =
        snapshot.parseFailedFiles.IsEmpty
        && (snapshot.diagnosticsByFile
            |> Map.toSeq
            |> Seq.collect snd
            |> Seq.forall (fun d -> not (blockingCodes.Contains d.code)))
        && (snapshot.semanticDiagnosticsByFile
            |> Map.toSeq
            |> Seq.collect snd
            |> Seq.forall (fun d -> not (blockingCodes.Contains d.code)))

    /// Decides whether the candidate snapshot may become the active rules
    /// model. `ruleFiles` is the overlay-merged rule file list the game model
    /// would be rebuilt from.
    let decideActivation
        (snapshot: CwtProjectSnapshot)
        (ruleFiles: (string * string) list)
        (active: CwtActiveRules option)
        : CwtActivationDecision =
        let candidateHash = contentHash ruleFiles

        match active with
        | Some current when current.contentHash = candidateHash -> NoChange
        | _ ->
            if not (candidateIsUsable snapshot defaultBlockingCodes) then
                let blockers =
                    snapshot.parseFailedFiles
                    @ (snapshot.diagnosticsByFile
                       |> Map.toSeq
                       |> Seq.collect snd
                       |> Seq.filter (fun d -> defaultBlockingCodes.Contains d.code)
                       |> Seq.map (fun d -> d.code)
                       |> Seq.distinct
                       |> Seq.toList)
                    @ (snapshot.semanticDiagnosticsByFile
                       |> Map.toSeq
                       |> Seq.collect snd
                       |> Seq.filter (fun d -> defaultBlockingCodes.Contains d.code)
                       |> Seq.map (fun d -> d.code)
                       |> Seq.distinct
                       |> Seq.toList)
                Rejected(blockers |> String.concat ", ")
            else
                Activate
