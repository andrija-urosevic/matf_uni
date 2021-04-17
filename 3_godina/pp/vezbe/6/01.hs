type Tacka = (Float, Float)
type Putanja = [Tacka]

data Kvadrant = PrviKvadrant 
              | DrugiKvadrant 
              | TreciKvadrant 
              | CetvrtiKvadrant 
              | KoordPocetak 
                deriving (Show, Read, Eq)

tacka :: Float -> Float -> Tacka
tacka x y = (x, y)

putanja :: [Tacka] -> Putanja
putanja = id

duzinaPutanje :: Putanja -> Int
duzinaPutanje = length

translirajTacku :: Tacka -> Float -> Float -> Tacka
translirajTacku (x, y) dx dy = tacka (x + dx) (y + dy)

rastojanje :: Tacka -> Tacka -> Float
rastojanje (x1, y1) (x2, y2) = sqrt $ (x1 - x2)^2 + (y1 - y2)^2

uKrugu :: Float -> [Tacka] -> [Tacka]
uKrugu r = filter (\t -> rastojanje (tacka 0 0) t < r)

translirajPutanju :: Putanja -> Float -> Float -> Putanja
translirajPutanju p dx dy = [translirajTacku t dx dy | t <- p]

translirajPutanju' :: Putanja -> Float -> Float -> Putanja
translirajPutanju' p dx dy = map (\t -> translirajTacku t dx dy) p

centroid :: [Tacka] -> Tacka
centroid tacke = tacka (artSredina $ map fst tacke) (artSredina $ map snd tacke) 
    where artSredina l = (sum l) / fromIntegral (length l)

nadovezi :: Tacka -> Putanja -> Putanja
nadovezi = (:)

spojiPutanje :: Putanja -> Putanja -> Putanja
spojiPutanje = (++)

kvadrantTacke :: Tacka -> Kvadrant
kvadrantTacke (x, y) 
    | x > 0 && y > 0 = PrviKvadrant
    | x < 0 && y > 0 = DrugiKvadrant
    | x < 0 && y < 0 = TreciKvadrant
    | x > 0 && y < 0 = CetvrtiKvadrant
    | otherwise      = KoordPocetak

tackeUKvadrantu :: Kvadrant -> [Tacka] -> [Tacka]
tackeUKvadrantu kvadrant = filter (\t -> kvadrantTacke t == kvadrant)

tackeVanKvadrantu :: Kvadrant -> [Tacka] -> [Tacka]
tackeVanKvadrantu kvadrant = filter (\t -> kvadrantTacke t /= kvadrant)

maksimalni :: [Tacka] -> Tacka
maksimalni tacke = (maximum $ map fst tacke, maximum $ map snd tacke)

qsort :: [Int] -> [Int]
qsort [] = []
qsort [x] = [x]
qsort (x:xs) = qsort [y | y <- xs, y <= x] ++ [x] ++ qsort [y | y <- xs, y > x]


