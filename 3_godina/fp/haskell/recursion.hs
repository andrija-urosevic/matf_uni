maximum' :: (Ord a) => [a] -> a
maximum' [] = error "Empty list!"
maximum' [x] = x
maximum' (x:xs) = max x (maximum' xs)

replicate' :: (Ord a, Num a) => a -> b -> [b]
replicate' n x 
    | n <= 0 = []
    | otherwise = x:(replicate' (n-1) x)

take' :: Int -> [a] -> [a]
take' n _
    | n <=0 = error "n <= 0"
take' n (x:xs) = x:(take (n-1) xs)

reverse' :: [a] -> [a]
reverse' [] = []
reverse' (x:xs) = (reverse' xs) ++ [x]

repeat' :: a -> [a]
repeat' x = x:(repeat' x)

zip' :: [a] -> [b] -> [(a,b)]
zip' _ [] = []
zip' [] _ = []
zip' (x:xs) (y:ys) = (x,y):(zip' xs ys)

elem' :: (Eq a) => a -> [a] -> Bool
elem' a [] = False
elem' a (x:xs)
    | a == x = True
    | otherwise = elem' a xs

quicksort' :: (Ord a) => [a] -> [a]
quicksort' [] = []
quicksort' (x:xs) = 
    let smallerThenPivot = [a | a <- xs, a <= x]
        biggerThenPivot = [a | a <- xs, a > x]
    in quicksort' smallerThenPivot ++ [x] ++ quicksort' biggerThenPivot



