import qualified Data.List as L

varijacije :: (Integral a) => [b]-> a -> [[b]]
varijacije xs 0 = [[]] 
varijacije xs k = concat $ map (\x -> map (x:) ys) xs
    where ys = varijacije xs (k - 1)

prosekOdlicnih :: [[Integer]] -> Float
prosekOdlicnih ocene = 
    let prosecneOcene   = map (\l -> fromIntegral (sum l) / fromIntegral (length l))
        odlicniProseci  = filter (\prosek -> prosek > 4.5)
        prosek          = \l -> realToFrac (sum l) / fromIntegral (length l)
    in prosek $ odlicniProseci $ prosecneOcene ocene

pozicije :: (Eq a) => a -> [a] -> [Int]
pozicije = L.elemIndices

pozicije' :: (Eq a) => a -> [a] -> [Int]
pozicije' e [] = []
pozicije' e l = [i | (x, i) <- zip l [0..n], x == e]
    where n = length l

qsort :: (Ord a) => [a] -> [a]
qsort [] = []
qsort (x:xs) = qsort levoOdPivota ++ jednakiPivotu ++ qsort desnoOdPivota
    where levoOdPivota  = filter (<x)  xs
          desnoOdPivota = filter (>x)  xs
          jednakiPivotu = filter (==x) (x:xs)

brisiPonavljanja :: (Eq a) => [a] -> [a]
brisiPonavljanja l = foldr (\x (y:ys) -> if x == y then y:ys else x:y:ys) [last l] l

podlistePonavljanja :: (Eq a) => [a] -> [[a]]
podlistePonavljanja []     = []
podlistePonavljanja (x:xs) = ponavljajuci : podlistePonavljanja ostatak 
    where ponavljajuci = x : takeWhile (==x) xs
          ostatak      = dropWhile (==x) xs

broj :: [Int] -> Int
broj = foldl (\acc x -> acc*10 + x) 0

brojObrnuto :: [Int] -> Int
brojObrnuto = foldr (\x acc -> acc*10 + x) 0

listaUPar :: [(a, b)] -> ([a], [b])
listaUPar l = (zene, muskarci)
    where zene     = map fst l
          muskarci = map snd l

parOdListi :: [a] -> [b] -> [(a, b)]
parOdListi [] _  = []
parOdListi _  [] = []
parOdListi (x:xs) (y:ys) = (x, y) : parOdListi xs ys

ucesljaj :: [a] -> [a] -> [a]
ucesljaj [] _  = []
ucesljaj _  [] = []
ucesljaj (x:xs) (y:ys) = x:y : ucesljaj xs ys


