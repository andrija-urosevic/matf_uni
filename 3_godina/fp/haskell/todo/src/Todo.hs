module Todo 
    ( dispach 
    ) where

import System.Directory
import System.IO
import Data.List

dispach :: [(String, ([String] -> IO ()))]
dispach = [ ("add", add)
          , ("list", list)
          , ("remove", remove)
          , ("bump", bump)
          ]

add :: [String] -> IO ()
add [fileName, todoItem] =
    appendFile fileName $ todoItem ++ "\n"

list :: [String] -> IO ()
list [fileName] = do
    content <- readFile fileName
    let todos       = lines content
        todoList    = zipWith (\n line -> show n ++ "-" ++ line) [0..] todos
    putStrLn $ unlines todoList
    

remove :: [String] -> IO ()
remove [fileName, numberString] = do
    handle                      <- openFile fileName ReadMode
    content                     <- hGetContents handle
    (tempFileName, tempHendle)  <- openTempFile "." "temp"
    let number      = read numberString
        todos       = lines content
        newTodos    = delete (todos !! number) todos
    hPutStr tempHendle $ unlines newTodos
    hClose handle
    hClose tempHendle
    removeFile fileName
    renameFile tempFileName fileName
        

bump :: [String] -> IO ()
bump [fileName, numberString] = do
    handle                      <- openFile fileName ReadMode
    content                     <- hGetContents handle
    (tempFileName, tempHandle)  <- openTempFile "." "temp"
    let number      = read numberString
        todos       = lines content
        todoToBump  = todos !! number
        newTodos    = todoToBump : (delete todoToBump todos)
    hPutStr tempHandle $ unlines newTodos
    hClose handle
    hClose tempHandle
    removeFile fileName
    renameFile tempFileName fileName


