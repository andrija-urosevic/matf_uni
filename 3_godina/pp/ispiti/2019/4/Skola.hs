import Data.List

type Ocene = [Int]
type Ucenik = (String, Ocene)

numPassed :: [Int] -> Int
numPassed ocene = length $ filter (>1) ocene

best :: [Ucenik] -> [String]
best lst =
    let bestStud = filter (\(_,ocene) -> numPassed ocene >= 2) lst
    in map fst bestStud


order :: [Ucenik] -> [(Int, String, Int)]
order lst = 
    let imeBrojPolozenih = map (\(ime, ocene) -> (ime, numPassed ocene)) lst
        maxBrojPolozenih = maximum $ map snd imeBrojPolozenih
    in map (\(ime, brojPolozenih) -> (maxBrojPolozenih - brojPolozenih + 1, ime, brojPolozenih)) imeBrojPolozenih
