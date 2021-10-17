module Input 
    ( getInput 
    ) where

import Data.Maybe (fromJust)

import UI.NCurses

data Input = Feed
           | Play
           | Quit
           | Idle
           deriving Show

getInput :: Curses Input
getInput = let maybeInput = \w -> event2Input . fromJust <$> getEvent w Nothing
           in defaultWindow >>= maybeInput >>= \i -> case i of
                                                  Just input -> pure input
                                                  Nothing    -> getInput
    where event2Input (EventCharacter 'f') = Just $ Feed
          event2Input (EventCharacter 'p') = Just $ Play
          event2Input (EventCharacter 'q') = Just $ Quit
          event2Input (EventCharacter '.') = Just $ Idle
          event2Input _                    = Nothing

