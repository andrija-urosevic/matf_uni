parni :: Integral a => a -> a -> [a]
parni a b = filter even [a..b]

neparni :: Integral a => a -> a -> [a]
neparni a b = filter odd [a..b]

parovi :: Integral a => a -> a -> a -> a -> [(a,a)]
parovi a b c d = [(x, y) | x <- [a..b], y <- [c..d]]

zavisnoY :: Integral a => a -> a -> [(a,a)]
zavisnoY a b = [(x, y) | x <- [a..b], y <- [x..b]]

bezbedanRep :: [a] -> [a]
bezbedanRep []      = []
bezbedanRep (x:xs)  = xs

bezbedanRep' :: Eq a => [a] -> [a]
bezbedanRep' l 
    | l == []   = []
    | otherwise = tail l

bezbedanRep'' :: Eq a => [a] -> [a]
bezbedanRep'' l = if (l == []) then [] else tail l

savrseni :: Integral a => a -> [a]
savrseni n = filter savrsen [1..n]
    where savrsen k = 
            let delioci = [x | x <- [1..k-1], k `mod` x == 0] 
            in sum delioci == k

zbirPar :: Integral a => a -> [(a, a)]
zbirPar n = [(a, b) | a <- [1..n-1], b <- [1..n-1], a + b == n]

poslednji :: [a] -> a
poslednji = head . reverse

-- [[asd, dsad], [sad, sda]] -> [asd, dsad, sad, sda]

spoji :: [[a]] -> [a]
spoji = foldl (++) [] 

sufiksi :: [a] -> [[a]]
sufiksi [] = [[]]
sufiksi l = l : (sufiksi . tail) l

izbaci :: Int -> [a] -> [a]
izbaci k l = prviDeoListe ++ drugiDeoListe
    where prviDeoListe = take (k-1) l
          drugiDeoListe = drop k l

ubaci :: Int -> a -> [a] -> [a]
ubaci k elem l = prviDeoListe ++ elem:drugiDeoListe
    where prviDeoListe = take k l
          drugiDeoListe = drop k l


