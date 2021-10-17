type Racun = (String, Int)

otvori :: [Racun] -> String -> [Racun]
otvori banka br_racuna = (br_racuna, 0) : banka

zatvori :: [Racun] -> String -> [Racun]
zatvori banka br_racuna = 
    foldr (\(br, i) acc -> if br == br_racuna 
                           then acc 
                           else (br, i) : acc) 
        [] banka

uplati :: [Racun] -> String -> Int -> [Racun]
uplati banka br_racuna iznos = 
    foldr (\(br, i) acc -> if br == br_racuna 
                           then (br, i + iznos) : acc 
                           else (br, i) : acc) 
        [] banka
