uvecaj :: Num a => [a] -> [a]
uvecaj = map (+1)

--[1,2,3,4] [a, b, c, d] -> [(1,a), (2,b), (3,c), (4,c)]
spoji :: [a] -> [b] -> [(a,b)]
spoji [] _ = []
spoji _ [] = []
spoji (x:xs) (y:ys) = (x,y) : spoji xs ys

pozitivna :: (Num a, Ord a) => [a] -> [a]
pozitivna = filter (>0)

prviNegativni :: (Num a, Ord a) => [a] -> [a]
prviNegativni = takeWhile (<0)

sumaListe :: (Num a) => [a] -> a
sumaListe = foldl (+) 0

-- [[1,2,3], [-2,-3,-1]] -> [6, 6]
absSume :: Num a => [[a]] -> [a]
absSume = map (abs . sum)

elem' :: (Eq a) => a -> [a] -> Bool
elem' e []      = False
elem' e (x:xs)  = if e == x then True else elem' e xs

elem'' :: (Eq a) => a -> [a] -> Bool
elem'' e = or . map (==e)

elem''' :: (Eq a) => a -> [a] -> Bool
elem''' x = any (==x)

