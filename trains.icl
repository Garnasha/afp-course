module trains

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

///////////////////////////////////
//SNIPPETS
///////////////////////////////////

/*
instance Applicative m | Monad m 
where
    pure x = return x
    (<*>) mf mx = mx >>= \x.mf >>= \f. return (f x)

instance Functor f | Applicative f
where
    fmap f fx = (<*> o pure) f fx
*/

///////////////////////////////////
//UTILITY
///////////////////////////////////
flip f x y :== f y x


//This crashes the compiler, probably some recursion in generic derivation
//derive class iTask UNIT
//Workaround:
:: GUNIT = GUNIT
derive class iTask GUNIT


instance TMonad TaskValue where
    (>>|) mx f = mx >>= \_.f
    (>>=) NoValue f = NoValue
    (>>=) (Value x sx) f = stabAnd (f x) sx
    where
        stabAnd NoValue _ = NoValue
        stabAnd (Value fx sfx) sx = Value fx (sfx && sx)
    
instance TApplicative TaskValue where
    return x = Value x True 
    (<#>) mf mx = mx >>= \x.mf >>= \f. return (f x)

instance TFunctor TaskValue where
    tmap f tx = ((<#>) o return) f tx


//tjoin :: (t (t a)) -> (t a) | TMonad t //this somehow causes an unsolvable internal overloading of (>>=)
tjoin mx = mx >>= id

//a variant on tjoin which discards outer stability
unpackTv :: (TaskValue (TaskValue a)) -> TaskValue a
unpackTv NoValue = NoValue
unpackTv (Value tvx _) = tvx //note: outer stability is ignored

blindType = flip (@) (const GUNIT)

/////////////////////////////////////
//TASK COMBINATORS
/////////////////////////////////////

//(-||-) :: (Task a) -> (Task a) -> Task a
//(-&&-) :: (Task a) -> (Task b) -> Task (a,b)
//(-&|&-) :: (Task a) -> (Task b) -> Task (TaskValue a,TaskValue b)
(-&|&-) infixr 4 :: !(Task a) !(Task b) -> (Task (TaskValue a,TaskValue b)) | iTask a & iTask b
(-&|&-) taska taskb
	= parallel
		[(Embedded, \_ -> taska @ Left),(Embedded, \_ -> taskb @ Right)] [] @? res
    where 
	    res (Value [(_,Value (Left a) sa),(_,Value (Right b) sb)] _)   = Value (Value a sa,Value b sb) (sa && sb)
        res (Value [(_,va),(_,vb)] _) = Value (fmap fromLeft va,fmap fromRight vb) False
       // res (Value [(_,NoValue),(_,NoValue)] _) = Value (NoValue,NoValue) False
	   // res (Value [(_,NoValue),(_,Value (Right b) sb)] _)   = Value (NoValue,Value b sb) False
	   // res (Value [(_,Value (Left a) sa),(_,NoValue)] _)   = Value (Value a sa,NoValue) False
        //res ab=:(Value _ sta,Value _ stb) = Value ab (sta && stb)
        fromLeft (Left x) = x
        fromRight (Right y) = y


//co@?, except not infix. Transforms TaskValues before consumption by TaskCont 
//similarly to how @? transforms TaskValues after production by Tasks
coatq :: ((TaskValue a) -> (TaskValue b)) (TaskCont b c) -> (TaskCont a c)
coatq prep (OnValue next) = OnValue (next o prep)
coatq prep (OnAction act next) = OnAction act (next o prep)
coatq _ (OnException handler) = OnException handler
coatq _ (OnAllExceptions handler) = OnAllExceptions handler

//fuses TaskCont lists for steppability from the result of a (-&|&-) chain
//NOTE: this must have the same infix direction as (-&|&-)
(>||>) infixr 4 :: [(TaskCont a c)] [(TaskCont b c)] -> [(TaskCont (TaskValue a,TaskValue b) c)]
(>||>) tcas tcbs = fmap (coatq (unpackTv o fmap fst)) tcas ++ fmap (coatq (unpackTv o fmap snd)) tcbs

///////////////////////////////////
//USER CONTROL
///////////////////////////////////


kickIfVal kickmsg kickto = OnValue (ifValue id (\_.viewInformation (Title "Kicked") [] kickmsg >>= kickto))

isMemberWithShared x share = watch share @ isMember x

:: Name	:== String
                                                          
ActionDriver = (Action "Driver" []) 

enterChoiceFromRoles = 
    viewInformation (Title "Choose a role") [] GUNIT ||- watch trains >>*
    [OnAction ActionDriver (ifValue (not o isEmpty) \_.trainSelect)]
    
trainSelect = enterChoiceWithShared (Title "Choose a train") [] trains

///////////////////////////////////
//TRAINS
///////////////////////////////////

:: Train = {name :: Name, loc :: Coords, dir :: Direction}
:: Direction :== Either GUNIT GUNIT

derive class iTask Train

trains :: Shared [Train]
trains = sharedStore "Trains" []

enterNewTrain :: Task Name
enterNewTrain = (enterInformation "New user:" [] >>* 
    [OnAction ActionOk (hasValue (
    \n.upd (prepend n) names ||- 
    return n))])
    where
        prepend :: String [String] -> [String]
        prepend s ss = [s:ss]



///////////////////////////////////
//GRID
///////////////////////////////////
:: Coords :== (!Int,!Int)
////////////////////////////////////////////////////////////

names :: Shared [Name]
names = sharedStore "UserNames" []

ideaCount :: Shared Int
ideaCount = sharedStore "IdeaCount" 1

okMask :: (Task a) -> Task a | iTask a
okMask t = (t >>* [OnAction ActionOk (hasValue return)])



nameSelection :: Task Name
nameSelection = okMask (enterChoiceWithShared "Returning user:" [] names) -||- enterNewUser

enterNewUser :: Task Name
enterNewUser = (enterInformation "New user:" [] -&&- watch names)>>* 
    [OnAction ActionOk (ifValue (not o uncurry isMember) (
    \(n,_).upd (prepend n) names ||- 
    return n))]
    where
        prepend :: String [String] -> [String]
        prepend s ss = [s:ss]

doShareIdentified :: (Name -> Task a) -> Task a  | iTask a
doShareIdentified task = nameSelection >>* [OnValue (hasValue task)]

//listSharePrepend :: (Shared [a]) a -> Task a  | iTask a
listSharePrepend share newval = upd (\shared.[newval:shared]) share

adminTask = blindType (updateSharedInformation "Admin" [] names)
userTask name = blindType (viewInformation (Title "Logged in as:") [] name)


/*
sharedMain name = ((if (name == "admin") adminTask (userTask name)) >>* 
    [OnValue (ifValue (const False) (\_.return GUNIT))]) -&|&- (watch names @ not o isMember name) >>*
    [OnValue (ifValue (pulldown o snd) (\_.(viewInformation (Title "Kicked") [] "Your account was deleted" >>| sharedTask)))]
    where 
        pulldown (Value True _) = True
        pulldown _ = False
        tempsnd (_,(Value True _)) = True
        tempsnd _ = False
        user_deleted (_,Value noms _) 
            | not (isMember name noms) = True
            | otherwise = False
        user_deleted _ = False
*/

sharedMain name = (if (name == "admin") adminTask (userTask name)) -&|&- (isMemberWithShared name names @ not) >>* 
    [] >||> [OnValue (ifValue id kickstep)]
    where 
        kickstep _ = viewInformation (Title "Kicked") [] "Your account was deleted" >>| sharedTask


sharedTask = blindType (doShareIdentified sharedMain)

Start :: *World -> *World
Start world = startEngine sharedTask world                             


///////////////////////////////////
//COMPLETE BUT UNUSED
///////////////////////////////////

//misguided attempt to strip the outer "TaskValue" on the right-hand inner tuple.
//However, the outer TaskValue on the tuple is actually useful to make types match, giving tjoin/unpackTv something to eat
(-|&&-) infixr 4 :: !(Task a) !(Task (TaskValue b,TaskValue c)) -> (Task (TaskValue a,(TaskValue b,TaskValue c))) | iTask a & iTask b & iTask c
(-|&&-) taska taskb
	= parallel
		[(Embedded, \_ -> taska @ Left),(Embedded, \_ -> taskb @ Right)] [] @? res
    where 
	    res (Value [(_,Value (Left a) sa),(_,Value (Right b) sb)] _)   = Value (Value a sa,b) (sa && sb)
        res (Value [(_,va),(_,Value (Right b) _)] _) = Value (fmap fromLeft va,b) False
        fromLeft (Left x) = x

////////////////////////////////
//DEAD CODE ONLY
////////////////////////////////
        /*
//Note: (++) and ViewWith reverse both have issues, but this was a fun learning experience.
parallelTask :: [NamedIdea] Int Name -> Task [NamedIdea] 
parallelTask ilist number name = 
    viewInformation "The result" [ViewWith reverse] ilist ||- 
    enterInformation (name +++ " add your idea") [] >>=
    \idea.parallelTask [packIdea number name idea:ilist] (number+1) name
    where
        packIdea number name idea = nameIdea number name idea

*/
/*
sharedMain :: Name -> Task [NamedIdea]
sharedMain name 
| name == "admin" = updateSharedInformation "Admin override on idea list:" [] ideas -||
    updateSharedInformation "Admin override on user list" [] names
| otherwise =
    (((enterChoiceWithShared "Ideas" [ChooseWith (ChooseFromGrid strip_idesc)] ideas >&^ 
    viewSharedInformation "Selected Idea" []) ||- 
    (viewInformation "Test" [] (isMember name ["Sal","admin"])) ||- 
    editIdea name 0 @? justify) -&&- (watch names)) >>* [
        OnAction ActionOk (ifValue (\(i,_).isJust i) 
        (\(idea,_).(fillInNumber (fromJust idea) >>= listSharePrepend ideas) ||- sharedMain name)),
        OnAction (Action "Clear" []) (always (sharedMain name)),
        OnAction ActionDelete (always 
        (confirmDelete >>* [OnValue (hasValue (\_.sharedMain name))])),
        OnAction ActionQuit (always (get ideas)),
        OnValue (user_deleted (get ideas))
        ]
        where 
            user_deleted atask (Value (_,noms) _)
            | isMember name noms = Nothing
            | otherwise = Just atask
            user_deleted _ _ = Nothing
            justify NoValue = Value Nothing False
            justify (Value x stab) = Value (Just x) stab
*/


//  sharedMain :: Name -> Task [NamedIdea]
//  sharedMain name 
//  | name == "admin" = updateSharedInformation "Admin override on idea list:" [] ideas -||
//      updateSharedInformation "Admin override on user list" [] names
//  | otherwise = anyTask [(watch names >>* [OnValue (user_deleted (return []))]),
//      (((enterChoiceWithShared "Ideas" [ChooseWith (ChooseFromGrid strip_idesc)] ideas >&^ 
//      viewSharedInformation "Selected Idea" []) ||- 
//      (viewInformation "Test" [] (isMember name ["Sal","admin"])) ||- 
//      editIdea name 0) >>* [
//          OnAction ActionOk (hasValue
//          (\idea.(fillInNumber idea >>= listSharePrepend ideas) ||- sharedMain name)),
//          OnAction (Action "Clear" []) (always (sharedMain name)),
//          OnAction ActionDelete (always 
//          (confirmDelete >>* [OnValue (hasValue (\_.sharedMain name))])),
//          OnAction ActionQuit (always (get ideas))
//         // OnValue (user_deleted (get ideas))
//          ])             ]
//          where 
//              user_deleted atask (Value noms _)
//              | isMember name noms = Nothing
//              | otherwise = Just atask
//              user_deleted _ _ = Nothing
//
/*
strip_idesc :: NamedIdea -> IdeaOverview
strip_idesc idea = { num = idea.number, idea_title = idea.idea.idea_name, owner = idea.user}

    

//This... does not solve race conditions, but should reduce the "race window" to ping.
fillInNumber :: NamedIdea -> Task NamedIdea   
fillInNumber idea = get ideaCount >>= 
    \count.upd ((+) 1) ideaCount ||- return { number = count, idea = idea.idea, user = idea.user }

:: IdeaOverview = { num :: Int, idea_title :: String, owner :: Name }

derive class iTask IdeaOverview
*/

/*
confirmDelete = viewInformation "Confirmation" [] "Do you really want to delete all ideas?" >>* [
    OnAction (Action "Yes" []) (always (set 1 ideaCount >>| set [] ideas)),
    OnAction (Action "No" []) (always (get ideas))
    ]
    */
