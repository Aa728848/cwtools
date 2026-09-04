namespace CWTools.Process.Localisation

open CWTools.Process.Scopes
open CWTools.Common
open CWTools.Process.Scopes.Scopes

module HOI4 =

    let scopedLocEffects () =
        [ ScopedEffect(
              "controller",
              [ scopeManager.ParseScope () "State" ],
              scopeManager.ParseScope () "Country",
              EffectType.Link,
              defaultDesc,
              "",
              true
          )
          ScopedEffect(
              "capital",
              [ scopeManager.ParseScope () "State" ],
              scopeManager.ParseScope () "State",
              EffectType.Link,
              defaultDesc,
              "",
              true
          )
          ScopedEffect(
              "owner",
              [ scopeManager.ParseScope () "UnitLeader"; scopeManager.ParseScope () "State" ],
              scopeManager.ParseScope () "Country",
              EffectType.Link,
              defaultDesc,
              "",
              true
          ) ]

    let scopedLocEffectsMap () = EffectMap.FromList(scopedLocEffects ())


    let locPrimaryScopes () =
        let from =
            fun (s, change) ->
                { s with
                    Scopes = scopeManager.AnyScope :: s.Scopes },
                true

        let prev = fun (s, change) -> { s with Scopes = s.PopScope }, true

        [ "This", id
          "Root", (fun (s, change) -> { s with Scopes = s.Root :: s.Scopes }, true)
          "Prev", prev
          "From", from //TODO Make it actually use FROM
          "FromFrom", from >> from
          "FromFromFrom", from >> from >> from
          "FromFromFromFrom", from >> from >> from >> from ]

    let locStaticSettings commands variableCommands (localisationLinks: (string * Scope list * Scope) list) =
        ChangeLocScope.createDefaultLegacyLocStaticSettings (locPrimaryScopes ()) (scopedLocEffectsMap ()) commands variableCommands localisationLinks
