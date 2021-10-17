module Main where

import Data.Char

--main :: IO ()
--main = do
    --putStrLn "Zdravo!\nKako ti je ime?"
    --ime <- getLine
    --putStrLn "Kako ti je prezime?"
    --prezime <- getLine
    --let imeVeliko = map toUpper ime
        --prezimeVelikko = map toUpper prezime
        --imePrezime = imeVeliko ++ " " ++ prezimeVelikko
    --putStrLn $ "Drago mi je, " ++ imePrezime ++ "!"
    
main :: IO ()
main = do
    line <- getLine
    if null line
        then return ()
        else do
            putStrLn $ reverseWords line
            main

reverseWords :: String -> String
reverseWords = unwords . map reverse . words
