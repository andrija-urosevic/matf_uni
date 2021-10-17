module Main where

import UI.NCurses

main :: IO ()
main = runCurses $ do
    setEcho False
    setCursorMode CursorInvisible
    w <- defaultWindow
    updateWindow w $ do
        moveCursor 1 10
        drawString "HelloWorld"
        moveCursor 3 10
        drawString "(pres q to quit)"
        moveCursor 0 0
    render
    waitFor w (\ev -> ev == EventCharacter 'q' 
                   || ev == EventCharacter 'Q')

waitFor :: Window -> (Event -> Bool) -> Curses ()
waitFor w p = loop 
    where loop = do
            event <- getEvent w Nothing
            case event of
                Nothing -> loop
                Just ev'-> if p ev' then return () else loop



