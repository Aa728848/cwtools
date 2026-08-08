namespace CWTools.Games.EU5

open CWTools.Games
open CWTools.Common
open CWTools.Games.Jomini
open CWTools.Localisation
open CWTools.Localisation.EU5

type EU5Settings = GameSetupSettings<JominiLookup>

type EU5Game(setupSettings: EU5Settings) =
    inherit
        JominiGame(
            setupSettings,
            { gameName = "europa universalis 5"
              defaultLang = EU5 EU5Lang.English
              oneToOneScopes = CWTools.Process.Scopes.EU5.oneToOneScopes
              oneToOneScopesNames = CWTools.Process.Scopes.EU5.oneToOneScopesNames
              localisationService = (EU5LocalisationService >> (fun f -> f :> ILocalisationAPICreator))
              scriptFolders = [| "common"; "events" |]
              afterInit = (fun _ -> ())
              includeModifierValidators = true })
