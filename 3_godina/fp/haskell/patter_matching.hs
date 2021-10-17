lucky :: (Integral a) => a -> String  
lucky 7 = "LUCKY NUMBER SEVEN!"  
lucky x = "Sorry, you're out of luck, pal!"   

faktorijel :: (Integral a) => a -> a
faktorijel 0 = 1
faktorijel n = n * faktorijel (n - 1)

f x
  | x <= 10 = -1
  | x <= 20 = -2
  | otherwise = -x
