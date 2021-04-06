import qualified Data.Map as Map

data Point = Point Float Float deriving (Show)
data Shape = Circle Point Float 
           | Rectangle Point Point 
           deriving (Show)

surface :: Shape -> Float
surface (Circle _ r) = 2 * r * pi
surface (Rectangle (Point x1 y1) (Point x2 y2)) = (abs $ x1 - x2) * (abs $ y1 - y2)

transform :: Shape -> Point -> Shape
transform (Circle (Point x y) r) (Point a b) = Circle (Point (x+a) (y+b)) r
transform (Rectangle (Point x1 y1) (Point x2 y2)) (Point a b) = Rectangle (Point (x1+a) (y1+b)) (Point (x2+a) (y2+b))

baseCircle :: Float -> Shape
baseCircle r = Circle (Point 0 0) r

baseRectangle :: Float -> Float -> Shape
baseRectangle w h = Rectangle (Point 0 0) (Point w h)

data Person = Person { firstname :: String
                     , lastname :: String
                     , age :: Int
                     , height :: Float
                     , number :: String
                     , icecream :: String 
                     } deriving (Eq, Show)


data Vector a = Vector a a a deriving (Show)

vecSum :: (Num a) => Vector a -> Vector a -> Vector a 
vecSum (Vector x y z) (Vector a b c) = Vector (x+a) (y+b) (z+c)

vecMult :: (Num a) => Vector a -> a -> Vector a
vecMult (Vector x y z) a = Vector (a*x) (a*y) (a*z)

data Dan = Ponedeljak | Utorak | Sreda | Cetvrtak | Petak | Subota | Nedelja deriving (Show, Read, Eq, Ord, Bounded, Enum)

type Ime = String
type Broj = String
type Imenik = [(Ime, Broj)]

uImeniku :: Ime -> Broj -> Imenik -> Bool
uImeniku ime broj imenik = elem (ime, broj) imenik


data OrmaricStanje = Zauzeto | Slobodno deriving (Show, Eq, Ord)

type Kod = String
type OrmaricMapa = Map.Map Int (OrmaricStanje, Kod)

pregledOrmarica :: Int -> OrmaricMapa -> Either String Kod 
pregledOrmarica brojOrmarica mapa = 
    case Map.lookup brojOrmarica mapa of
        Nothing -> Left $ "Ormaric broj " ++ show brojOrmarica ++ " ne postoji!"
        Just (stanje, kod) -> 
            if stanje == Zauzeto 
                then Left $ "Ormaric broj " ++ show brojOrmarica ++ " je zauzet!"
                else Right kod

infixr 5 :+:
data Lista a = Prazna | a :+: (Lista a) deriving (Show, Read, Eq, Ord)

data Drvo a = PraznoDrvo | Cvor a (Drvo a) (Drvo a) deriving (Show, Read)

noviCvor :: a -> Drvo a
noviCvor x = Cvor x PraznoDrvo PraznoDrvo

ubaciCvor :: (Ord a) => a -> Drvo a -> Drvo a
ubaciCvor x PraznoDrvo = noviCvor x
ubaciCvor x (Cvor a levo desno)
    | x == a = Cvor x levo desno
    | x < a  = Cvor a (ubaciCvor x levo) desno
    | x > a  = Cvor a levo (ubaciCvor x desno)

elemtCvor :: (Ord a) => a -> Drvo a -> Bool
elemtCvor x PraznoDrvo = False
elemtCvor x (Cvor a levo desno)
    | x == a = True
    | x < a  = elemtCvor x levo
    | x > a  = elemtCvor x desno

data Semafor = Crveno | Zuto | Zeleno

instance Eq Semafor where
    Crveno == Crveno    = True
    Zuto   == Zuto      = True
    Zeleno == Zeleno    = True
    _      == _         = False 

instance Show Semafor where
    show Crveno = "Crveno svetlo"
    show Zuto   = "Zuto svetlo"
    show Zeleno = "Zeleno svetlo"

class DaNe a where
    dane :: a -> Bool

instance DaNe Int where
    dane 0 = False
    dane _ = True

instance DaNe [a] where
    dane [] = False
    dane _  = True

instance DaNe Bool where
    dane = id

instance DaNe (Maybe a) where
    dane Nothing  = False
    dane (Just _) = True

instance DaNe (Drvo a) where
    dane PraznoDrvo = False
    dane _          = True

instance DaNe Semafor where
    dane Crveno = False 
    dane _      = True 


