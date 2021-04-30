type Str = [Char]
type Tacka = (Float, Float)

data Bul = Tacno 
         | Netacno
         deriving Show

negiraj :: Bul -> Bul
negiraj Tacno = Netacno
negiraj Netacno = Tacno

data Krug = MkKrug { r :: Float}
data Pravougaonik = MkPravougaonik { a :: Float, b :: Float } 

class Oblik a where
    povrsina :: a -> Float
    obim :: a -> Float

instance Oblik Krug where
    povrsina k = (r k)^2 * pi
    obim     k = 2 * (r k) * pi

instance Oblik Pravougaonik where
    povrsina p = (a p) * (b p)
    obim     p = 2 * ((a p) + (b p))

instance Eq Krug where
    k1 == k2 = (r k1) == (r k2)

instance Eq Pravougaonik where
    p1 == p2 = ((a p1) == (a p2)) && ((b p1) == (b p2))

instance Show Krug where
    show k = "Krug(r=" ++ show (r k) ++ ")"

instance Show Pravougaonik where
    show p = "Pravougaonik(a=" ++ show (a p) ++ ",b=" ++ show (b p) ++ ")"

data Osoba = MkOsoba { ime :: String
                     , prezime :: String
                     , godine :: Int
                     , visina :: Float
                     } deriving Show


infixr 7 :::
data Lista a = PraznaLista | a ::: (Lista a) deriving Show


