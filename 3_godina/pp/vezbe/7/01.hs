import qualified Data.List as L
import Data.Maybe

data StepenStudija = Osnovne
                   | Master
                   | Doktorske
                   deriving (Eq)

data Student = Student
    { indeks        :: String
    , ime           :: String
    , prezime       :: String
    , stepenStudija :: StepenStudija 
    }

type Rezultat = (Student, Maybe Int)

prikaziStepenStudija :: StepenStudija -> String
prikaziStepenStudija Osnovne    = "BSc."
prikaziStepenStudija Master     = "MSc."
prikaziStepenStudija Doktorske  = "PhD."

prikaziStudent :: Student -> String
prikaziStudent student =
    let indeksStudenta  = indeks student
        imePrezime      = ime student ++ " " ++ prezime student
        stepenStudenta  = show $ stepenStudija student
    in indeksStudenta ++ ": " ++ stepenStudenta ++ " " ++ imePrezime 

instance Show StepenStudija where
    show = prikaziStepenStudija

instance Show Student where
    show = prikaziStudent

instance Eq Student where
    student1 == student2 = indeks student1 == indeks student2

rezultatiInit :: [Student] -> [Rezultat]
rezultatiInit = map (\student -> (student, Nothing))

poeni :: Student -> [Rezultat] -> Either String Int
poeni student rezultati = 
    let indeks = L.elemIndex student $ map fst rezultati
    in if indeks == Nothing then
        Left $ "Student " ++ show student ++ " se ne nalazi u listi!"
    else 
        let poeni = map snd rezultati !! fromJust indeks
        in if poeni == Nothing then
            Right $ 0
        else
            Right $ fromJust $ poeni

ponisti :: Student -> [Rezultat] -> [Rezultat]
ponisti student = foldr ponisti []
    where ponisti s acc =
            if fst s == student 
            then (student, Nothing):acc 
            else s:acc 

ponistiSve :: [Rezultat] -> [Rezultat]
ponistiSve = map (\s -> (fst s, Nothing))

studije :: StepenStudija -> [Rezultat] -> [Rezultat]
studije stepen = filter (\s -> (stepenStudija (fst s)) == stepen)

polozeni :: [Rezultat] -> [Rezultat]
polozeni = filter (\s -> snd s /= Nothing)

upisi :: Student -> Int -> [Rezultat] -> [Rezultat]
upisi student poeni rezultati = 
    if elem student studenti
    then foldr azuriraj [] rezultati
    else (student, Just poeni):rezultati
        where studenti = map fst rezultati
              azuriraj s acc = 
                if fst s == student 
                then (student, Just poeni):acc
                else s:acc

najbolji :: Int -> [Rezultat] -> [Int]
najbolji n = take n
           . L.sortBy (\_ _ -> GT)
           . map fromJust
           . filter (\s -> s /= Nothing)
           . map snd

marko = Student 
    { indeks = "mi12313"
    , ime = "Marko"
    , prezime = "Markovic"
    , stepenStudija = Master 
    }

pera = Student 
    { indeks = "mi11233"
    , ime = "Pera"
    , prezime = "Peric"
    , stepenStudija = Doktorske 
    }

zika = Student 
    { indeks = "mi21313"
    , ime = "Zika"
    , prezime = "Sarenica"
    , stepenStudija = Doktorske 
    }

rezultati = rezultatiInit [marko, pera]



