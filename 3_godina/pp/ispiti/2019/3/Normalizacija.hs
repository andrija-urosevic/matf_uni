getmax :: [Float] -> Float
getmax lst = 
    foldl (\acc el -> if acc <= el 
                      then el
                      else acc) 
        (head lst) lst

getmin :: Ord a => [a] -> a
getmin lst =
    foldl (\acc el -> if acc >= el
                      then el
                      else acc)
        (head lst) lst

normalize :: [Float] -> Float -> Float -> [Float]
normalize lst newMin newMax = 
    let oldMin = getmin lst
        oldMax = getmax lst
    in map (\e -> (e - oldMin)*(newMax - newMin)/(oldMax - oldMin) + newMin) lst

