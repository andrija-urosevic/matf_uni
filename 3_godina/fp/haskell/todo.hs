import Data.List

dispach :: [(String, ([String] -> IO ()))]
dispach = [ ("--add", add)
          , ("--list", list)
          , ("--remove", remove)
          ]

add :: [String] -> IO ()
add s = return ()

list :: [String] -> IO ()
list s = return ()

remove :: [String] -> IO ()
remove s = return ()



