module Banka 
    ( Transakcija(..)
    , AktivneTransakcije
    , izlistaj
    , dodaj
    , ukloni
    , ukupno
    ) where

data Transakcija = Transakcija
    { ident :: Int
    , iznos :: Int
    , posiljac :: String
    , primalac :: String
    } deriving (Show, Eq)

type AktivneTransakcije = [Transakcija]

izlistaj :: AktivneTransakcije -> String -> [Transakcija]
izlistaj aktivne_transakcije broj_racuna =
    filter (\transakcija -> posiljac transakcija == broj_racuna 
                         || primalac transakcija == broj_racuna)
        aktivne_transakcije

dodaj :: AktivneTransakcije -> Transakcija -> AktivneTransakcije
dodaj aktivne_transakcije transakcija = transakcija : aktivne_transakcije

ukloni :: AktivneTransakcije -> Int -> AktivneTransakcije
ukloni aktivne_transakcije id = 
    filter (\transakcija -> ident transakcija /= id) aktivne_transakcije

ukupno :: AktivneTransakcije -> Int
ukupno = foldl (\acc transakcija -> iznos transakcija + acc) 0
