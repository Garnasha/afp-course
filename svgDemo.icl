module svgDemo

/*
	Pieter Koopman pieter@cs.ru.nl
	Advanced programming, advanced iTask, 2016
	Demo program for SVG and a share
	
	This is an iTask program:
	- use environment iTasks
	- place the executable in the iTasks-SDK folder or a subfolder of it
	- the SVG system can use much memory, for instance 50M (in project options)
*/

import iTasks
import iTasks.API.Extensions.SVG.SVGlet

Start :: *World -> *World
Start world = startEngine [publish "/" (WebApp []) (\_ -> task)] world

:: State = {red :: Bool, clicks :: Int}
derive class iTask State

state :: Shared State
state = sharedStore "sharedState" {red = False, clicks = 0}

task :: Task State
task
	= (		(updateTask <<@ ArrangeHorizontal)
	-||-	(imageTask  <<@ ArrangeHorizontal)) <<@ ArrangeHorizontal

// regular iTask update of shared state
updateTask :: Task State
updateTask = updateSharedInformation (Title "State") [] state

// display the shared state as an image and update it
imageTask :: Task State
imageTask =
	updateSharedInformation
		(Title "Image")
		[imageUpdate
			id												// server state (share) and view are identical
			(\s v tags -> myImage s)	// generate image
			(\s v -> v)								// update view when state changes
			(\s v -> s)								// update state when view changes
			(\_ s -> Nothing)					// no conflict handling
			(\o n.n)									// always select the new state
		]
		state

myImage :: State -> Image State
myImage s = 
	overlay [(AtMiddleX,AtMiddleY)] [] [text font (toString s.clicks)]
	(Just (circle (px 100.0)
					<@< {fill = toSVGColor (if s.red "orangered" "lightgreen")}
					<@< {onclick = \i s.{s & clicks = i + s.clicks, red = not s.red}, local = False}
			  ))

font = normalFontDef "Arial" 18.0

