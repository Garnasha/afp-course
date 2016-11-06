module ideabox

/*
	Pieter Koopman, pieter@cs.ru.nl
	Advanced Programming.
	Skeleton for assignment 5.
	* To be used in a project with the environment iTasks.
	* The executable must be inside the iTask-SDK directory of the Clean distribution, 
	  or one of its subdirectories. You can either put your program there, or use the
	  set executable option of the Project Options.
	* You can also use the -sdk commandline flag to set the path.
	  Example: -sdk C:\Users\johndoe\Desktop\Clean2.4\iTasks-SDK

*/

import iTasks
import StdArray // for the size of a String


flip f x y :== f y x

:: Idea	= { idea_name :: String, idea_description :: Maybe Note } 
:: Name	:== String

:: NamedIdea = { number :: Int, idea :: Idea, user :: Name}

//:: NumberedIdea = {number :: Display Int,nidea :: NamedIdea}

derive class iTask Idea
derive class iTask NamedIdea
//derive class iTask NumberedIdea


doIdentified :: (Name -> Task x) -> Task x | iTask x
doIdentified task
	=   enterInformation "Enter your name" []
	>>= task // >>= for sequential composition of tasks


parallelInit = doIdentified (parallelTask [] 1)

//Note: (++) and ViewWith reverse both have issues, but this was a fun learning experience.
parallelTask :: [NamedIdea] Int Name -> Task [NamedIdea] 
parallelTask ilist number name = 
    viewInformation "The result" [ViewWith reverse] ilist ||- 
    enterInformation (name +++ " add your idea") [] >>=
    \idea.parallelTask [packIdea number name idea:ilist] (number+1) name
    where
        packIdea number name idea = nameIdea number name idea

////////////////////////////////////////////////////////////
nameIdea number user idea = {number = number,idea = idea, user = user}

editIdea :: Name Int -> Task NamedIdea
editIdea name i =   
    enterInformation (name +++ ", add your idea") [] @ nameIdea i name 

ideas :: Shared [NamedIdea]
ideas = sharedStore "Ideas" []

names :: Shared [Name]
names = sharedStore "UserNames" []

ideaCount :: Shared Int
ideaCount = sharedStore "IdeaCount" 1

okMask :: (Task a) -> Task a | iTask a
okMask t = (t >>* [OnAction ActionOk (hasValue return)])



nameSelection :: Task Name
nameSelection = okMask (enterChoiceWithShared "Returning user:" [] names) -||- enterNewUser

enterNewUser :: Task Name
enterNewUser = (enterInformation "New user:" [] >>* 
    [OnAction ActionOk (hasValue (
    \n.upd (prepend n) names ||- 
    return n))])
    where
        prepend :: String [String] -> [String]
        prepend s ss = [s:ss]

doShareIdentified :: (Name -> Task a) -> Task a  | iTask a
doShareIdentified task = nameSelection >>* [OnValue (hasValue task)]

//listSharePrepend :: (Shared [a]) a -> Task a  | iTask a
listSharePrepend share newval = upd (\shared.[newval:shared]) share

//  sharedMain :: Name -> Task [NamedIdea]
//  sharedMain name 
//  | name == "admin" = updateSharedInformation "Admin override on idea list:" [] ideas -||
//      updateSharedInformation "Admin override on user list" [] names
//  | otherwise =
//      (((enterChoiceWithShared "Ideas" [ChooseWith (ChooseFromGrid strip_idesc)] ideas >&^ 
//      viewSharedInformation "Selected Idea" []) ||- 
//      (viewInformation "Test" [] (isMember name ["Sal","admin"])) ||- 
//      editIdea name 0 @? justify) -&&- (watch names)) >>* [
//          OnAction ActionOk (ifValue (\(i,_).isJust i) 
//          (\(idea,_).(fillInNumber (fromJust idea) >>= listSharePrepend ideas) ||- sharedMain name)),
//          OnAction (Action "Clear" []) (always (sharedMain name)),
//          OnAction ActionDelete (always 
//          (confirmDelete >>* [OnValue (hasValue (\_.sharedMain name))])),
//          OnAction ActionQuit (always (get ideas)),
//          OnValue (user_deleted (get ideas))
//          ]
//          where 
//              user_deleted atask (Value (_,noms) _)
//              | isMember name noms = Nothing
//              | otherwise = Just atask
//              user_deleted _ _ = Nothing
//              justify NoValue = Value Nothing False
//              justify (Value x stab) = Value (Just x) stab
//


sharedMain :: Name -> Task [NamedIdea]
sharedMain name 
| name == "admin" = updateSharedInformation "Admin override on idea list:" [] ideas -||
    updateSharedInformation "Admin override on user list" [] names
| otherwise = ((watch names ) -||
    (((enterChoiceWithShared "Ideas" [ChooseWith (ChooseFromGrid strip_idesc)] ideas >&^ 
    viewSharedInformation "Selected Idea" []) ||- 
    (viewInformation "Test" [] (isMember name ["Sal","admin"])) ||- 
    editIdea name 0) >>* [
        OnAction ActionOk (hasValue
        (\idea.(fillInNumber idea >>= listSharePrepend ideas) ||- sharedMain name)),
        OnAction (Action "Clear" []) (always (sharedMain name)),
        OnAction ActionDelete (always 
        (confirmDelete >>* [OnValue (hasValue (\_.sharedMain name))])),
        OnAction ActionQuit (always (get ideas))
       // OnValue (user_deleted (get ideas))
        ])) >>* [OnValue (user_deleted (return []))]
        where 
            user_deleted atask (Value noms _)
            | isMember name noms = Nothing
            | otherwise = Just atask
            user_deleted _ _ = Nothing
  

strip_idesc :: NamedIdea -> IdeaOverview
strip_idesc idea = { num = idea.number, idea_title = idea.idea.idea_name, owner = idea.user}

confirmDelete = viewInformation "Confirmation" [] "Do you really want to delete all ideas?" >>* [
    OnAction (Action "Yes" []) (always (set 1 ideaCount >>| set [] ideas)),
    OnAction (Action "No" []) (always (get ideas))
    ]
    

//This... does not solve race conditions, but should reduce the "race window" to ping.
fillInNumber :: NamedIdea -> Task NamedIdea   
fillInNumber idea = get ideaCount >>= 
    \count.upd ((+) 1) ideaCount ||- return { number = count, idea = idea.idea, user = idea.user }

:: IdeaOverview = { num :: Int, idea_title :: String, owner :: Name }

derive class iTask IdeaOverview



sharedTask = doShareIdentified sharedMain

Start :: *World -> *World
Start world = startEngine sharedTask world                             


enterNewTrain :: Task Name
enterNewTrain = (enterInformation "New user:" [] >>* 
    [OnAction ActionOk (hasValue (
    \n.upd (prepend n) names ||- 
    return n))])
    where
        prepend :: String [String] -> [String]
        prepend s ss = [s:ss]
