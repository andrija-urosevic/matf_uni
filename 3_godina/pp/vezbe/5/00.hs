main = print "Zdravo"

duplo n = 2 * n
duplo' n = (*) 2 n
duplo'' = (*) 2
duplo''' = (*2)

ostatak3 :: Int -> Int
ostatak3 n = mod n 3

puta = (*)

mnoze3broja x y z = x `puta` y `puta` z
mnoze3broja' x y z = puta (puta x y) z

korenCeli :: Int -> Double
korenCeli n = sqrt (fromIntegral n)

sumaPrvih :: Int -> Int
sumaPrvih 0 = 0
sumaPrvih n = (+) n (sumaPrvih (n - 1))

sumaPrvih' :: Int -> Int
sumaPrvih' n = 
    if n == 0 then 
        0 
    else 
        (+) n (sumaPrvih (n-1))

sumaPrvih'' :: Int -> Int
sumaPrvih'' n
    | n == 0    = 0
    | otherwise = (+) n (sumaPrvih (n-1))

sumaPrvih''' :: Int -> Int
sumaPrvih''' n = foldl (+) 0 [1..n]

lepDan :: String -> Bool 
lepDan dan
    | dan == "Subota"   = True
    | dan == "Nedelja"  = True
    | otherwise         = False


lepDan' :: String -> Bool 
lepDan' "Subota"    = True
lepDan' "Nedelja"   = True
lepDan' _           = False 

parMax :: (Int, Int) -> Int
parMax (a, b) = if a > b then a else b
parMax x = if fst x > snd x then fst x else snd x
parMax x = max (fst x) (snd x)
parMax (a, b) = max a b

elem e [] = False
elem e (x:xs) = if x == e then True else elem e xs
