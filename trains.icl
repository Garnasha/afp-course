module trains

/*
    Sal Wolffs, sal.wolffs@gmail.com
	Based on a skeleton by Pieter Koopman, pieter@cs.ru.nl
	* To be used in a project with the environment iTasks.
	* The executable must be inside the iTask-SDK directory of the Clean distribution, 
	  or one of its subdirectories. You can either put your program there, or use the
	  set executable option of the Project Options.
	* You can also use the -sdk commandline flag to set the path.
	  Example: -sdk C:\Users\johndoe\Desktop\Clean2.4\iTasks-SDK

*/

//I've given up. 
//Spent some time figuring out what kind of combinator I needed to achieve 
//some guarantees on drivers (specifically, you can't drive a deleted train).  
//
//Couldn't find any combinator with the right type. Took some learning to be
//able to write my own and make it suitable for the general case. Added some 
//more utilities. Decided on and defined the datastructure to be used. 
//
//I had planned to define the drawing functions recursively... and when the 
//time came to do so, in the planning stage of writing the first draw function, 
//"draw interactive Sign", I ran into the final problem: oh, right, the state
//fed to an Image m must be a Shared m. Which takes a Lens, or equivalent code. 
//And SDSLenses are yet another new thing. Which can't be found by type because
//their type is so convoluted that Cloogle doesn't recognize them when searched
//for as something like :: (Shared a) (a -> b) (b -> a) -> Shared b .
//
//I underestimated this project, and am now well over 16 hours into it. 
//I don't have the clock time anymore to turn it into anything meriting a 
//passing grade, let alone one able to significantly improve any passing 
//exam grade. I never truly had the labour time available to learn two 
//DSLs in two weeks using only a search engine, one which is not optimized 
//for those DSLs. 
//
//

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

($) infixr 0 :: !(.a -> .b) !.a -> .b
($) f x = f x

//Not quite the way I'd have liked it but... better than (!!)
class `at` f where
    (`at`) infixl 9 :: (Maybe (f a)) !Int -> Maybe a

instance `at` [] where
    (`at`) (Just xs) i 
    | i < 0 = Nothing
    | i > length xs = Nothing
    | otherwise = Just (xs !! i)
    (`at`) _ _ = Nothing

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

collapseTvMaybe NoValue = NoValue
collapseTvMaybe (Value Nothing _) = NoValue
collapseTvMaybe tv = tv


//a variant on tjoin which discards outer stability
unpackTv :: (TaskValue (TaskValue a)) -> TaskValue a
unpackTv NoValue = NoValue
unpackTv (Value tvx _) = tvx //note: outer stability is ignored

blindTask = flip (@) (const Void)

/////////////////////////////////////
//TASK COMBINATORS
/////////////////////////////////////

//Parallel bind, which is likely actually monadic
(>&=) infixl 1 :: (Task a) (a -> Task b) -> Task b   | iTask a & iTask b
(>&=) taska ataskb = taska >&> flip whileUnchanged (nothingToNoVal ataskb)
    where
        nothingToNoVal _ Nothing = return Void @? const NoValue
        nothingToNoVal atb (Just x) = atb x


//(-&&-) :: (Task a) -> (Task b) -> Task (a,b)
(-&|&-) infixr 2 :: !(Task a) !(Task b) -> (Task (TaskValue a,TaskValue b)) | iTask a & iTask b
(-&|&-) taska taskb
	= parallel
		[(Embedded, \_ -> taska @ Left),(Embedded, \_ -> taskb @ Right)] [] @? res
    where 
	    res (Value [(_,Value (Left a) sa),(_,Value (Right b) sb)] _)   = Value (Value a sa,Value b sb) (sa && sb)
        res (Value [(_,va),(_,vb)] _) = Value (fmap fromLeft va,fmap fromRight vb) False
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
(>||>) infixr 2 :: [(TaskCont a c)] [(TaskCont b c)] -> [(TaskCont (TaskValue a,TaskValue b) c)]
(>||>) tcas tcbs = fmap (coatq (unpackTv o fmap fst)) tcas ++ fmap (coatq (unpackTv o fmap snd)) tcbs

///////////////////////////////////
//USER CONTROL
///////////////////////////////////

kickOnTrue kickmsg kickto = OnValue (ifValue id (\_.viewInformation (Title "Kicked") [] kickmsg >>| kickto))

isMemberWithShared x share = watch share @ isMember x

:: Name	:== String
                                                          
ActionDriver = Action "Driver" [] 
ActionController = Action "Controller" []
ActionDesigner = Action "Designer" []
ActionAdmin = Action "Admin" []


enterChoiceFromRoles = blindTask $
    viewInformation (Title "Choose a role") [] Void ||- watch trains  >>*
    [OnAction ActionDriver (ifValue (not o isEmpty) \_.trainSelect),
    OnAction ActionController (always controllerTask),
    OnAction ActionDesigner (always designerTask),
    OnAction ActionAdmin (always adminTask)]
    
trainSelect = blindTask $
    enterChoiceWithShared (Title "Choose a train") [ChooseWith (AutoChoice trainName)] trains -&|&- (watch trains @ isEmpty) >>*
    [OnAction ActionOk (hasValue driverTask)] >||> [kickOnTrue "The last train was deleted" enterChoiceFromRoles]

///////////////////////////////////
//ENTITIES
///////////////////////////////////

derive class iTask Coords, Cardinal, Train, Tile, Track, Edge, Signal

//TRAINS
////////////////

:: Direction :== Bool //right || up && !(left)
:: Train = {tname :: Display Name, loc :: Display Coords, dir :: Direction, dest :: String}


trainName :: Train -> Name
trainName train = fromDisplay train.tname

trainLoc train = fromDisplay train.loc


trains :: Shared [Train]
trains = sharedStore "Trains" []

:: TrainEntry = {train_name :: Name, facing_right_or_straight_up :: Direction, destination :: String}
derive class iTask TrainEntry

addTrain :: Tile -> Task Train
addTrain tile = enterInformation "Add train on selected tile:" [EnterWith (onTile tile)] >>* 
    [OnAction ActionOk (ifValue (\_.isNothing tile.train) (\train.upd (prepend train) trains @! train))]
    where
        prepend s ss = [s:ss]
        onTile tile tentry = 
            {tname = Display tentry.train_name, loc = Display tile.pos, dir=tentry.facing_right_or_straight_up, dest=tentry.destination}



//GRID
////////////////
:: Coords = {x :: !Int,y :: !Int}


:: Layout :== [[Tile]]

baseLayout = [[baseTile]]

layoutShare :: Shared Layout
layoutShare = sharedStore "layout" baseLayout

getTile coords = get layoutShare @ toTile coords @? collapseTvMaybe
watchTile coords = watch layoutShare @ toTile coords @? collapseTvMaybe

toTile coords lay = return lay `at` coords.x `at` coords.y


//TILES
////////////////

:: Cardinal = N | E | S | W

:: Tile = {label :: String, pos :: Coords, track :: Track, train :: Maybe Train}

baseTile = {label="Home",pos={x=0,y=0},track = NoTrack, train = Nothing}



//TRACKS
////////////////

//Decision: Points act as two Segments, of which one active, and as such, Points take Signals.
:: Track = NoTrack | Terminal Edge | Segment Edge Edge | Point Edge Edge Edge

activeTrack (Point base active _) = Segment base active
activeTrack x = x

toggleTrackPoint (Point base active inactive) = Point base active inactive

//EDGES
////////////////

:: Edge = {side :: Cardinal, signal :: Signal}



//SIGNALS
////////////////

:: Signal = Green | Red | Disabled

///////////////////////////////////
//ROLES
///////////////////////////////////

//Driver
/////////////////
driverTask train = blindTask $
    viewInformation (Title "Driver") [] ("Train: " +++ trainName train)


//Controller
/////////////////
controllerTask = blindTask $
    viewInformation (Title "Controller") [] Void ||- (watch layoutShare @ hd o hd) >&= addTrain

//Designer
/////////////////
designerTask = blindTask $
    viewInformation (Title "Designer") [] Void

//Admin
/////////////////
adminTask = blindTask $
    updateSharedInformation (Title "Admin") [] names
////////////////////////////////////////////////////////////

names :: Shared [Name]
names = sharedStore "UserNames" []

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

userTask name = blindTask (viewInformation (Title "Logged in as:") [] name)


sharedMain name = (if (name == "admin") adminTask (userTask name)) -&|&- 
    (isMemberWithShared name names @ not) >>* 
    [] >||> [kickOnTrue "Your account was deleted" sharedTask]


forceMString :: (Maybe String) -> Maybe String
forceMString x = x
newBindDemo = (enterInformation (Title "Entry") []  <<@ ArrangeHorizontal  >&> 
    \s.(whileUnchanged s (viewInformation (Title "Output") [] o forceMString)  <<@ ArrangeHorizontal)) <<@ ArrangeHorizontal

oldBindDemo = enterInformation (Title "Entry") [] >>= viewInformation (Title "Output") [] o forceMString


//sharedTask = blindTask (doShareIdentified sharedMain)
//sharedTask = newBindDemo -&&- oldBindDemo
sharedTask = enterChoiceFromRoles

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
