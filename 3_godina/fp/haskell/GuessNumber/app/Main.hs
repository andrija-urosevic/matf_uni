module Main where

import GuessNumber
import System.Random

main :: IO ()
main = do
    gen <- getStdGen
    askForNumber gen
