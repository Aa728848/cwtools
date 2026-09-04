namespace CWTools.Process.Scopes

open CWTools.Common
open CWTools.Process.Scopes
open CWTools.Utilities.Utils2

module IR =

    let defaultDesc = "Scope (/context) switch"


    let scopedEffects =
        [
        // // To title
        // ScopedEffect("primary_title", [Scope.Character], Scope.Title, EffectType.Both, defaultDesc, "", true)
        // // To character
        // ScopedEffect("mother", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("mother_even_if_dead", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("father", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("father_even_if_dead", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("killer", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("liege", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("liege_before_war", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("top_liege", [Scope.Character], Scope.Character, EffectType.Both, defaultDesc, "", true)
        // // To province
        // ScopedEffect("capital_scope", [Scope.Character; Scope.Title], Scope.Province, EffectType.Both, defaultDesc, "", true)
        // ScopedEffect("owner", [Scope.Province], Scope.Character, EffectType.Both, defaultDesc, "", true);
        ]



    let oneToOneScopes = Scopes.jominiOneToOneScopes
    let oneToOneScopesNames = Scopes.jominiOneToOneScopesNames
    let changeScope: ChangeScope = Scopes.jominiChangeScope
