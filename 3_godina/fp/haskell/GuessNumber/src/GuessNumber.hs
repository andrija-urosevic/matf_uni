module GuessNumber
    ( askForNumber
    ) where

import System.Random
import Control.Monad (when)

askForNumber :: StdGen -> IO ()
askForNumber gen = do
    let (randNumber, newGen) = randomR (1, 10) gen :: (Int, StdGen)
    putStr "Guess number that I'm thinking of: "
    numString <- getLine
    when (not $ null numString) $ do
        let number = read numString
        if randNumber == number
            then putStrLn "You are correct!"
            else putStrLn $ "Sorry, I was thinking of " ++ show randNumber
        askForNumber newGen
    

