# Uvod

Sakupljanje ogromnog broja podataka neverovatno brzo raste, ali
sta nedostaje jestu metodi za izvlacenje korisnih informacijama 
iz velikog skupa podataka. Zbog toga tradicionalni alati za analizu
podataka nisu dovoljno sufisticirani, i novi moraju biti razvijeni.

Istrazivanje podataka je tehnologija koja spaja tradicionalnu 
analizu podataka sa sofisticiranim algoritmima za procesiranje
velike zapremine podataka.

**Biznisi**. Postoje mnogi alati za prikupljanje podataka potrosaca 
u realnom vremenu. Pa proizvodjaci mogu da iskoriste te informacije
za svoje potrebe, tako da naprave proizvod koji ce bolje odgovarati
korisniku. Ove informacije mogu takodje da daju odgovore na neka od
pitanja kao sto su: Ko su najprofitabilniji potrosaci? Koji proizvod
se bolje prodaje, a koji losije? Kolika je zarada kompanije za
tekucu godinu?

**Medicina, Nauka i Inzinjering**. Prikupljaju se podati koji su
kljucni za nova otkrica. Primer je NASA koja je postavila satelite
oko planete Zemlje i meti kopno, okeane i atmosferu. Ali zvog
kolicine podataka tradicionalni metodi nisu korisni za analizu
ovakvig skupova podataka. Istrazivanje podataka moze da da odgovore
na sledeca pitanja: Koja je relacija izmedju frekvencije i 
intenziteta vremenskih neprilika kao sto su poplave i tornadi? Kako
je temperatura na kopnu u zavisnosti od temperature na povrsini 
okeana? Kako predvideti pocetak i kraj uzgajne sezone?

## Sta je istrazivanje podataka?

Istrazivanje podataka je proces automackog otkrivanja korisnih
informacija u velikim skladistenim podacima. Pronalazi nove i korisne
sablone koji bi mozda ostali neotkriveni. Takodje imaju mogucnost da
predvide buduca opazanja, kao sto je predvidjanje da li ce novi
potrosac potrositi vise od 1000din u radnji.

Nisu sva otkrivanja informacija istrazivanje podataka. Na primer,
jednostavni upit data baze ili nalazenje odredjene Web stranice 
preko pretrazivaca su zadaci oblasti koja se naziva *pronalazenje
informacija*. Oni jesu veoma korisni ali se oslanjaju na 
tradicionalne algoritme i strukture podataka.

### Istrazivanje podataka i otkrivanje znanja

Istrazivanje podataka je deo otkrivanja znanje u bazi podataka(KDD),
sto je proces dobijanja korisnih informacija iz sirovih podataka.

```
    Ulazni Podaci --> Predprocesiranje --> Istrazivanje Podataka 
                  --> Postprocesiranje --> Informacija
```

Uloga **predprocesiranja** je da transformise sirove podatke u
radne podatke koji su spremni za analizu. Ovo ukljucuje spajanje
podataka sa vise izvora, ciscenje podataka od suma i duplikata,
biranje karakteristika koji su relevantni za istrazivanje podataka.

Takodje nakon instrazivanja podataka potrebno je rezultat 
interpretirati, i ovaj proces se naziva **postprocesiranje**. Primeri je vizualizacija.

## Izazovi u istrazivanju podataka

### Skalabilnost

Skupovi podataka se cuvaju u gigabajtima, terabajtima, pa cak i
petabajtma. Zbog taga tehnike istrazivanja podataka moraju biti
skalabilne. Mnogi algoritmi koriste specijalne strategije pretrage,
pa cak i implementacije novih struktura podataka koji pristupaju
slogovima efikasno.

### Velika Dimenzionalnost

Sada je cesto da se nadju skupovi podataka sa stotinama ili
hiljadama atributa. Za neke tradicionalne algoritme podataka,
njigova kompleksnost se povecava sa povecanjem dimenzija (broja 
atributa). Takodje, neki uopste ne daju dobre rezultate.

### Heterogeni i kompleksni podaci

Tradicionalni metodi analize podataka se primenjuju na skupove
podataka koji imaju atribute istog tipa. Kako se uloga istrazivanja
podataka povecava, povecava se potreba za obradjivanje heterogenih 
atributa. Takodje pojavljuju se i mnogi kompleksni podaci, kao sto
su XML dokumenti, grafovi...

### Pripadnost i distribucija podataka

Podaci ne moraju biti smesteni na jednoj lokaciji, takodje, ne
moraju ce ni da pripadaju jednoj organizaciji. Ovo zahteva 
distributivne tehnike istrazivanja podataka, tj. smanjenje 
komunikacije za distribuirano izvrsavanje, spajanje rezultata iz
vise izvora i sigurnosne probleme.

### Netradicionalna analiza

Za razliku od tradicionalnih statistickih metoda koji se baziraju na
hipotezi i testu, tj. iskaze se hipoteza, onda se dizajnira 
eksperiment koji prikuplja podatke, i onda se analiza sprovede po
iskazanoj hipoteze, noviji metodi analize podataka generisu i
evaluisu hiljade hipoteza, a i mnoge tehnike su napravljene tako da
automatizuju ovaj proces.

## Nastanak istrazivanja podataka

Istrazivanje podataka se oslanja na idejama kao st su 
  1. uzorkovanje, ocenjivanje, i testiranje hipoteza iz statistike
  2. algoritmi pretrage, tehnike modelovanja, i teorija ucenja
     iz vestacke inteligencije, prepoznavanje sablona, i masinsko
     ucenje.
Takodje potrebne su i dodatne oblasti racunarstva kao sto su
sistemi baza podataka, paralelnog izracunavanja, distributivno
programiranje.

## Zadatak istrazivanja podataka

**Zadatak predvidjanja**. Predvidja vrednost nekog atributa bazirano
na vrednostima drugih atributa. Atribut koji se predvidja naziva
se **target** ili **zavisna promenljiva**, dok atributi koji se 
koriste za predvidjanje se nazivaju **opisni** ili **nezavisne 
promenljive**.

**Zadatak opisivanja**. Izvlaci sablone koji sumiraju relacije
izmedju podataka.

**Model predvidjanja** se odnosi na izgradnju modela za target 
promenljive kao funkcije koja prima ulazne promenljive. Postoje
dva zadatka modela predvidjanja: **klasifikacija** i **regresija**.
Klasifikacije se koristi za diskretnu vrednost target promenljive,
dok se regresija koristi za neprekidnu vrednost target promenljive.
Cilj oba zadatka je da minimizuju gresku izmedju predvidjenje
vrednosti i istinite vrednosti target promenljive.

**Primer (Predvidjanje vrsta Irisa)**. Za dati skup podataka koji
predstavlja cvet irisa, mozemo odrediti vrstu irisa na osnovu 
duzine i sirine latica.

**Asocijativna analiza** se koristi za otkrivanje sablona koji
opisuju pridruzene karakteristike u podacima. Sabloni se 
predstavljaju kao implicitno pravilo ili kao podskup karakteristika.

**Primer (Analiza korpe)**. Na osnovu podataka o kupovinama proizvoda
mozemo zakljuciti da ako je potrosac kupio Pampres, onda je i kupio
Mleko, pa imamo sledece pravilo ``{Pampers}->{Mleko}``.

**Klaster analiza** pronalazi grupe usko povezanih podataka tako
da podaci koja pripadaju istom klasteru su slicnija medjusobno
nego podaci nekog dugog klastera.

**Primer (Klasterovanje dokumenata)**. Mozemo da klasterujemo
artikle bazirano na njihovoj upotrebi. Na osnovu broj ponavljanja 
odredjene reci iz opisa artikla mozemo da zakljucimo svrhu tog
artikla. Na primer, ako sadrzi reci kao sto je ``medicinski, pacijent, lek, zdravlje,...`` mozemo ove artikle smestiti u jedan
klaster.

**Otkrivanje anomalija** je zadatak identifikovanje podataka cije
su karakteristike znacajno drugacije od ostalih podataka. Takvi
podaci se poznati kao *anomalije* ili *autlajeri*. Pri ovom procesu
moramo sto preciznije odrediti anomalije, u smislu da ne smemo
oznaciti normalne objekte kao anomalije, i suprotno.

**Primer (Kradja kreditne kartice)**. Banka skuplja podatke o 
transakcijama korisnika kreditne kartice, zajedno sa licnim 
informacijama korisnika. Na osnovu toga, moze zablokirati karticu 
ako dodje do transakcije koja je najmanje verovatna da se dogodi,
jer predstavlja potencionalnog kradljivca.

# Podaci

