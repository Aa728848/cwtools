namespace CWTools.Process.Scopes

open System
open CWTools.Common
open CWTools.Process.Scopes
open CWTools.Utilities
open CWTools.Utilities.Utils2

module STL =
    open CWTools.Utilities.Utils
    // open Microsoft.FSharp.Collections.Tagged

    let defaultDesc = "Scope (/context) switch"

    let oneToOneScopes =
        let from i =
            fun (s, change) ->
                let index = s.FromDepth + i
                { s with
                    FromDepth = index
                    Scopes = (s.GetFrom index) :: s.Scopes },
                struct (false, true)

        let prev = fun (s, change) -> { s with Scopes = s.PopScope }, struct (false, true)

        [ "THIS", id
          "ROOT", (fun (s, change) -> { s with Scopes = s.Root :: s.Scopes }, struct (false, true))
          "FROM", from 1
          "FROMFROM", from 2
          "FROMFROMFROM", from 3
          "FROMFROMFROMFROM", from 4
          "PREV", prev
          "PREVPREV", prev >> prev
          "PREVPREVPREV", prev >> prev >> prev
          "PREVPREVPREVPREV", prev >> prev >> prev >> prev ]

    let oneToOneScopesNames = List.map fst oneToOneScopes

    let private baseChangeScope: ChangeScope =
        Scopes.createChangeScope oneToOneScopes (Scopes.simpleVarPrefixFun "var:") true

    /// Colony resolves carrier to the synthetic Planet-or-Ship union. A direct
    /// Planet/Ship carrier lookup has no statically typed result and becomes Any.
    let changeScope: ChangeScope =
        ChangeScope(fun varLhs skipEffect links valueTriggers wildcards vars key source ->
            match baseChangeScope.Invoke(varLhs, skipEffect, links, valueTriggers, wildcards, vars, key, source) with
            | NewScope(target, ignored, hint) when
                String.Equals(target.CurrentScope.ToString(), "Carrier", StringComparison.OrdinalIgnoreCase)
                && (String.Equals(source.CurrentScope.ToString(), "Planet", StringComparison.OrdinalIgnoreCase)
                    || String.Equals(source.CurrentScope.ToString(), "Ship", StringComparison.OrdinalIgnoreCase))
                ->
                let anyScope = source.Root.AnyScope
                let scopes =
                    match target.Scopes with
                    | [] -> [ anyScope ]
                    | _ :: tail -> anyScope :: tail

                NewScope({ target with Scopes = scopes }, ignored, hint)
            | WrongScope(command, _, _, _) as wrongScope when
                String.Equals(command, "target", StringComparison.OrdinalIgnoreCase)
                ->
                // Situation/Agreement/Espionage target is bound to the event ROOT,
                // so it remains accessible from nested scopes such as System.
                let rootContext = { source with Scopes = [ source.Root ] }
                match baseChangeScope.Invoke(varLhs, skipEffect, links, valueTriggers, wildcards, vars, key, rootContext) with
                | NewScope({ Scopes = target :: _ }, ignored, hint) ->
                    NewScope({ source with Scopes = target :: source.Scopes }, ignored, hint)
                | _ -> wrongScope
            | result -> result)

    let sourceScope (effects: Map<StringLowerToken, Scope list>) (key: string) =
        let key =
            if key.StartsWith("hidden:", StringComparison.OrdinalIgnoreCase) then
                key.Substring(7)
            else
                key

        let keys = key.Split('.') |> List.ofArray

        let inner (nextKey: string) : Scope list option =
            // Strip trailing '?' for optional scope syntax (e.g., owner? = { ... })
            let nextKey = if nextKey.EndsWith('?') then nextKey.Substring(0, nextKey.Length - 1) else nextKey
            let onetoone = oneToOneScopes |> List.tryFind (fun (k, _) -> k == nextKey)
            let nextKey = StringResource.stringManager.InternIdentifierToken nextKey

            match onetoone with
            | Some _ -> None
            | None -> Map.tryFind nextKey.lower effects
        // match (effects
        // |> Seq.tryFind (fun e -> e.Name.lower = nextKey.lower)) with
        // | None -> None
        // | Some e -> Some e.Scopes

        keys
        |> List.fold
            (fun acc k ->
                match acc with
                | Some e -> Some e
                | None -> inner k)
            None
        |> Option.defaultValue scopeManager.AllScopes
