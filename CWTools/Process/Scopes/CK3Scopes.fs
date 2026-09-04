namespace CWTools.Process.Scopes

open CWTools.Common
open CWTools.Process.Scopes
open CWTools.Utilities.Utils2

module CK3 =




    let oneToOneScopes =
        let from i =
            fun (s, change) ->
                { s with
                    Scopes = (s.GetFrom i) :: s.Scopes },
                true

        let prev = fun (s, change) -> { s with Scopes = s.PopScope }, true
        let root = fun (s, change) -> { s with Scopes = s.Root :: s.Scopes }, true

        [ "THIS", id
          "ROOT", root
          "ROOT_FROM", root >> from 1
          "ROOT_FROMFROM", root >> from 2
          "ROOT_FROMFROMFROM", root >> from 3
          "ROOT_FROMFROMFROMFROM", root >> from 4
          "FROM", from 1
          "FROMFROM", from 2
          "FROMFROMFROM", from 3
          "FROMFROMFROMFROM", from 4
          "PREV", prev
          "PREVPREV", prev >> prev
          "PREVPREVPREV", prev >> prev >> prev
          "PREVPREVPREVPREV", prev >> prev >> prev >> prev ]

    let oneToOneScopesNames = List.map fst oneToOneScopes

    let changeScope: ChangeScope =
        Scopes.createJominiChangeScope oneToOneScopes (Scopes.complexVarPrefixFun "variable:from:" "variable:")
