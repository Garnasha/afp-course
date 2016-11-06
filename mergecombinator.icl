module mergecombinator

/*
    Sal Wolffs, sal.wolffs@gmail.com

	Usage notes (Pieter Koopman, pieter@cs.ru.nl):
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
//UTILITY
///////////////////////////////////
flip f x y :== f y x


//This crashes the compiler, probably some recursion in generic derivation
//derive class iTask UNIT
//Pity, because UNIT is the unit (final object) in the category of Clean types.
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
unpackTv (Value tvx _) = tvx 

blindType = flip (@) (const GUNIT)

/////////////////////////////////////
//TASK COMBINATORS
/////////////////////////////////////

//(-&&-) :: (Task a) -> (Task b) -> Task (a,b)
//(-&|&-) merges tasks similarly to (-&&-), but never collapses into NoValue.
(-&|&-) infixr 4 :: !(Task a) !(Task b) -> (Task (TaskValue a,TaskValue b)) | iTask a & iTask b
(-&|&-) taska taskb
	= parallel
		[(Embedded, \_ -> taska @ Left),(Embedded, \_ -> taskb @ Right)] [] @? res
    where 
	    res (Value [(_,Value (Left a) sa),(_,Value (Right b) sb)] _)   = Value (Value a sa,Value b sb) (sa && sb)
        res (Value [(_,va),(_,vb)] _) = Value (fmap fromLeft va,fmap fromRight vb) False
        fromLeft (Left x) = x
        fromRight (Right y) = y

//coatq is co@?, except not infix. Transforms TaskValues before consumption by TaskCont 
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

/////////////////////////////////////
//DEMO
/////////////////////////////////////

::Name :== String

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

adminTask = blindType (updateSharedInformation "Admin" [] names)
userTask name = blindType (viewInformation (Title "Logged in as:") [] name)

sharedMain name = (if (name == "admin") adminTask (userTask name)) -&|&- 
    (watch names @ not o isMember name) -&|&-
    (enterInformation (Title "Third task") []) 
    >>* 
    [] >||> 
    [OnValue (ifValue id kickstep)] >||> 
    [OnAction ActionOk (hasValue (viewInformation (Title "Result") [] o ((+++) "You completed the third task and entered: "))),
    OnValue (ifValue ((==) "secret") (\_.viewInformation (Title "Secret") [] "You entered the secret code!"))]
    where 
        kickstep _ = viewInformation (Title "Kicked") [] "Your account was deleted" >>| sharedTask


sharedTask = doShareIdentified sharedMain

Start :: *World -> *World
Start world = startEngine sharedTask world                             

