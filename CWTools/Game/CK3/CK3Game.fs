namespace CWTools.Games.CK3

open CWTools.Games
open CWTools.Common
open CWTools.Games.Jomini
open CWTools.Localisation
open CWTools.Localisation.CK3

type CK3Settings = GameSetupSettings<JominiLookup>

type CK3Game(setupSettings: CK3Settings) =
    inherit
        JominiGame(
            setupSettings,
            { gameName = "crusader kings iii"
              defaultLang = CK3 CK3Lang.English
              oneToOneScopes = CWTools.Process.Scopes.CK3.oneToOneScopes
              oneToOneScopesNames = CWTools.Process.Scopes.CK3.oneToOneScopesNames
              localisationService = (CK3LocalisationService >> (fun f -> f :> ILocalisationAPICreator))
              scriptFolders = [||]
              afterInit = (fun (game: JominiGameFunctions.GameObject) ->
                  game.Lookup.coreModifiers <- game.Settings.embedded.modifiers)
              includeModifierValidators = false })
