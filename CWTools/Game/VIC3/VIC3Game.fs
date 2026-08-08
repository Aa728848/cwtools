namespace CWTools.Games.VIC3

open CWTools.Games
open CWTools.Common
open CWTools.Games.Jomini
open CWTools.Localisation
open CWTools.Localisation.VIC3

type VIC3Settings = GameSetupSettings<JominiLookup>

type VIC3Game(setupSettings: VIC3Settings) =
    inherit
        JominiGame(
            setupSettings,
            { gameName = "victoria 3"
              defaultLang = VIC3 VIC3Lang.English
              oneToOneScopes = CWTools.Process.Scopes.VIC3.oneToOneScopes
              oneToOneScopesNames = CWTools.Process.Scopes.VIC3.oneToOneScopesNames
              localisationService = (VIC3LocalisationService >> (fun f -> f :> ILocalisationAPICreator))
              scriptFolders = [| "common"; "events" |]
              afterInit = (fun _ -> ())
              includeModifierValidators = true })
