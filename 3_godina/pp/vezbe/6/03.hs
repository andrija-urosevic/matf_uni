list_all :: (a -> Bool) -> [a] -> Bool
list_all p = and . map p

obrni :: [a] -> [a]
obrni = foldl (\acc x -> x:acc) []

delioci :: Integral a => a -> [a]
delioci n = [x | x <- [2..n-1], n `mod` x == 0]

prost :: Integral a => a -> Bool
prost n = length (delioci n) == 0

prosti :: Integral a => a -> [a]
prosti n = filter prost [2..n]

sufiks :: [a] -> [[a]]
sufiks = scanr (:) []

prefiks :: [a] -> [[a]]
prefiks l = map reverse $ scanl (\acc x -> x:acc) [] l

ukloniDuplikate :: (Eq a) => [a] -> [a]
ukloniDuplikate = reverse . foldl (\acc x -> if elem x acc then acc else x:acc) []

qsort :: (Ord a) => [a] -> [a]
qsort [] = []
qsort (x:xs) = qsort levoOdPivota ++ [x] ++ qsort desnoOdPivota
    where levoOdPivota = filter (>x) xs
          desnoOdPivota = filter (>=x) xs

