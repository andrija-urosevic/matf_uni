fib :: Integral a => a -> a 
fib 0 = 1
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

parni :: Integral a => a -> [a]
parni n = [2,4..2*n]

parni' :: Integral a => a -> [a]
parni' n = [2*x | x <- [1..n]]

parni'' :: Integral a => a -> [a]
parni'' n = [x | x <- [1..2*n], x `mod` 2 == 0]

fibLista :: Int -> [Int]
fibLista 0 = []
fibLista 1 = [1]
fibLista 2 = [1, 1]
fibLista n = fibListaN1 ++ [(fibListaN1 !! (n-3)) + (fibListaN1 !! (n-2))]
    where fibListaN1 = fibLista (n-1)

-- [1,1,2,3] ++ [2+3] -> [1,1,2,3,5]


jednocifreniDelioci :: Int -> [Int]
jednocifreniDelioci n = [x | x <- [1..9], n `mod` x == 0]




