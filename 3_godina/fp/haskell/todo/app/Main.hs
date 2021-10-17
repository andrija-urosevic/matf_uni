module Main where

import Todo 

import System.Environment

main :: IO ()
main = do
    (command:args) <- getArgs
    let Just action = lookup command dispach
    action args
