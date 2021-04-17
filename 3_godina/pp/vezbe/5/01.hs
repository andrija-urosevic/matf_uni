spoji :: [a] -> [a] -> [a]
spoji l [] = l
spoji [] l = l
spoji l (x:xs) = spoji (reverse (x:(reverse l))) xs

glava :: [a] -> a
glava [] = error "Ne moze od prazne"
glava (x:xs) = x

odbaci :: Integral a => a -> [b] -> [b]
odbaci 0 l = l
odbaci n [] = error "Nema dovoljno elemenata"
odbaci n (x:xs) = odbaci (n-1) xs

duzina :: Integral b => [a] -> b
duzina [] = 0
duzina (x:xs) = 1 + duzina xs

proizvodPrvih :: Integral a => a -> a
proizvodPrvih 0 = 1
proizvodPrvih n = n * proizvodPrvih (n-1)

prost :: Integral a => a -> Bool
prost 2 = True
prost n = deljivo n 2
    where deljivo n k 
            | n == k    = True
            | otherwise = if n `mod` k == 0 then False else deljivo n (k+1)

prost' :: Integral a => a -> Bool
prost' n = null $ listaDelioca
    where listaDelioca = [x | x<-[2..n-1], n `mod` x == 0]

nzd :: Integral a => a -> a -> a
nzd a 0 = a
nzd a b = nzd b (a `mod` b) 

tipJednacine a b c
    | d == 0    = "Jedno resenje"
    | d < 0     = "Nema resenja"
    | otherwise = "Dva resenja"
    where d = b^2 - 4*a*c
    
izDekadne :: Integral a => a -> a -> a
izDekadne 0 osn = 0
izDekadne x osn = (x `mod` osn) + 10 * izDekadne (x `div` osn) osn

harm :: (Enum a, Fractional a) => a -> [a]
harm n = [1/x | x<-[1..n]]
   
delioci :: Integral a => a -> [a]
delioci n = [x | x<-[2..n-1], n `mod` x == 0]

nadovezi :: Integral b => [a] -> [a] -> b -> [a]
nadovezi l1 l2 0 = l1
nadovezi l1 l2 n = nadovezi l1 l2 (n-1) ++ l2

sumaKvadrata :: Integral a => a -> a
sumaKvadrata 0 = 0
sumaKvadrata n = n^2 + sumaKvadrata (n-1)

sumaKvadrata' :: Integral a => a -> a
sumaKvadrata' n = sum [x^2 | x<-[1..n]]

sumaKvadrata'' :: Integral a => a -> a
sumaKvadrata'' n = foldl (\acc x -> acc + x^2) 0 [1..n]

