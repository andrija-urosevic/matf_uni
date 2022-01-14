# Objektno Orijentisano Programiranje

## Osnovni Koncepti OOP

### Objekti i Klase

**OMG**-*Object Management Group* definise objekte i klase kao:
* *Klasa* je opis skupa objekata koji dele iste atribute, operacije,
  metode, odnose i semantiku. Svrha klase je da deklarise kolekicju
  metoda, operacija i atributa koja u potpunosti opisuju strkutkuru
  i ponasanje tih objekata.
* *Objekat* je primerak koji potice iz klase, struktuiran je i ponasa
  se u skladu sa svojom klasom.

### Enkapsulacija i Interfejs

* *Enkapsulacija* predstavlja princip skrivanja detalja 
  implementacije klase od korisnika te klase.
* *Interfejs* klase predstavlja skup metoda koje korisnik moze da
  koristi kako bi se sakrila sama implementacija tih metoda.

### Specijalizacija i Generalizacija

* Klasa `A` *jeste* klasa `B` ako i samo ako svaki objekat klase `A`
  ima sve osobine koje imaju i svi objkti klase `B`.
  * Kazemo jos da je klasa `A` *izvedena* iz `B`, a da je klasa `B`
    *osnovna* klasa za `A`
  * Takodje, kazemo i da je klasa `A` *potomak* klase `B`, a da je
    klasa `B` *predak* klase `A`.
* Ako klasa `A` *jeste* klasa `B`, onda je `A` *specijalizacija*
  klase `B`, a klasa `B` je *generalizacija* klase `A`.

## OOP Metodologije

Tri osnovna perioda OOP metodologije:

1. *Pocetni koraci* pri definisanju razlicitih metodologija.
2. *Objedinjavanje* metodologija: UML. 
3. *Post-UML period*: agilne metodologije.

* entiteti --- sve vreste podataka koji postoje u softverskom sistemu
* subjekti --- razlicite vrste korisnika softverskog sistema
* servisi --- usluge koje softverski sistem pruza korisnicima
* interfejsi --- podsistemi putem kojih subjekti koriste servise

## Slabosti Objektno Orijentisanih Koncepata

* Tradicionalni nedostaci: velicina izvrsivog programa, brzina 
  inzvrsavanja programa, nesrazmerno veliki programerski rad.
* Treba voditi racuna kada se radi sa relacionim bazama podataka.
    * Sloj objektno-relacionog preslikavanja (*Object-Relationl Mapping --- OMR*)
* OOP koncepti nisu dovoljno teorijski definisani. 
* Problemi u hijerarhijskom polimorfizmu. Problem 
  kvadrat-pravouganik.
* Objekti grade implicitno globalno stanje programa.
* Teorija tipova: Objekte treba smatrati kao konstantne entitete
  koji ne mogu da promene svoje stanje.

# UML

## Objedinjeni Jezik za Modeliranje

* Objedinjeni jezik za modeliranje (*Unified Modeling Language --- UML*)
* Podela UML dijagrama:

1. strukturni dijagrami
2. dijagrami ponasanja

### Strukturni Dijagrami

Strukturni dijagrami opisuju strukturu softverskog sistema i 
njegovih delova.

* dijagram klasa (*class diagram*)
  * elementi statickog modela softvera
* dijagram objekata (*object diagram*)
  * dinamicka priroda izmedju objekata
* dijagram paketa (*package diagram*)
  * Logicka dekompozicija u pakete
    *Paket* --- prostor imena
* dijagram slozene strukture (*composite structure diagram*)
  * opisuju unutrasnju strukturu elemenata neke strukture
* dijagram komponenti (*component diagram*)
  * opisuje komponente koje cine aplikaciju, podsistem,...
  * funkcionalna dekompozicija
* dijagram isporucivanja (*diployment diagram*)
  * fizicka arhitektura softverskog sistema
* dijagram profila (*profile diagram*)
  * prilagodjavanje UML dijagrama specificnim domenskim problemima.

### Dijagrami Ponasanja

Dijagrami ponasanja se bave dinamickom prorodom softverskog
sistema.

* dijagram slucajeva upotrebe (*use case diagram*)
  * slucajevi upotrebe, akteri, i medjusobne osobine
* dijagram aktivnosti (*activity diagram*)
  * poslovni procesi viseg nivoa, tokovi podataka, i slozene logicke
    elemente sistema
* dijagram stanja (*state machine diagram*)
  * opisuje kako se stanje jednog objekta menja u zavisnosti
    od interakcija u koje objekat ulazi
* dijagram interakcije:
  * dijagram sekvence (*sequance diagram*)
    * precizno opisuje tok odvijanja slucajeva upotrebe, i jesno
      prepoznaje odgovornosti subjekta i objekta za pojedinacne
      korake
  * dijagram komunikacije (*communication diagram*)
    * ilustruje objekte, njihove medjusobne odnose i poruke koje
      razmenjuju
  * dijagram vremena (*timing diagram*)
    * promena stanja objekata za neko vreme.
  * pregledni dijagram interakcija (*interaction overview diagram*)
    * varijanta dijagrama aktivnosti, gde je akcenat na upravljanju
      procesima ili sistemom.

## Dijagram klasa

* *Dijagram klase* se predstavlja pravougaonicima, koji su podeljeni
  horizontalnim linijama: prvi deo sadrzi naziv klase,
  drugi sadrzi spisak polja klase, a treci spisak metoda klase.
* Vidljivost atributa i metoda se predstavlja nekim znakom:
  * `-` predstavlja privatni clan;
  * `+` predstavlja javni clan;
  * `#` predstavlja zasticeni clan;
* Neke clanove mozemo izostaviti ako nisu bitni, ali mozemo dodati i 
  novu sekciju za ogranicenja.
* Tipove clanova navodima sa znakom `:`.

![Dijagram klasa](res/uml1.png)

* *Agregacija* predstavlja *slabu integraciju*, jer je sacinjena od
  delova koji *mogu* da postoje nezavisno.
* *Kompozicija* predstavlja *jaku integraciju*, jer je sacinjena od 
  delova koji *ne mogu* da postoje nezavisno.
* *Asocijacija* predstavlja to da jedan objekat ima referencu
  na neki drugi objekat.
* *Zavisnost* predstavlja povezanost dva objekta koja nije trajna.


![Zavisnost izmedju klasa](res/uml2.png)


* *Stereotipi klase* navode se unutar `<< >>`.
  * *abstract* - apstraktna klasa
  * *auxilary* - pomocna klasa
  * *entity* - trajni podatak
  * *enumeration* - novi tip ogranicenog domena
  * *focus* - najvaznija klasa na dijagramu
  * *interface* - interfejs

### Vrste dijagrama klasa

* Dijagrami klase ne treba da obuhvataju celokupan sistem vec samo
  odredjene delove i relevantne informacije iz njega.
* Dijagram klase koji se bavi strukturom objekata, bez ponasanja 
  tog objekta naziva se *dijagram modela domena*.
* Dijagram klase koji se bavi ponasanjem objekata, bez strukture
  tog objekta naziva se *dijagram interfejsa klase*.

![Dijagram klasa *Lista*](res/uml3.png)

## Dijagram objekata

* *Dijagram objekata* sadrzi naziv klase, nazive objekata, imena i 
  vrednosti atributa i odnose medju objektima u jednom trenutku 
  vremena. 

![Dijagram objekta klase *Lista*](res/uml4.png)

## Dijagram komponenti

* *Dijagram komponenti* predstavlja funkcionalnu ili fizicku
  komponentu softvera.

## Dijagram slucajeva upotrebe

* *Dijagram slucajeva upotrebe* opisuje jednu funkcionalnu celinu
  sistema.
* Osnovni elementi:
  * *Slucajevi upotrebe* --- jedna celina koja je pracena 
    tekstualnom dokumentacijom.
  * *Akteri* --- korisnici koji koriste slucajeve upotrebe.
  * *Njihovi medjusobni odnosi*
    * *include*: slucaj obuhvata citav slucaj prema kome ide 
      strelica, obicno je to deo posla koji se ponavlja.
    * *extends*: slucaj od koga ide strelica predstavlja 
      opciono prosirenje drugog slucaj, obicno je to neki dodatak.

![Dijagram slucajeva upotrebe: *Studiranje*](res/uml5.png)

* Tekstualna dokumentacija slucajeva upotrebe treba da sadrzi bar:
  * naziv;
  * aktere;
  * kratak opis;
  * preduslove;
  * postuslove;
  * opis toka slucaja upotrebe;
  * opis posebnih slucajeve;
  * druge uml dijagrame;
* Tekstualna dokumentacija slucajeva upotrebe moze jos da sadrzi i:
  * klasifikacija
  * podaci
  * dodatne nefunkcionalne zahteva
  * bezbednosne karakteristike
  * pregled najvaznijih rizika
  * jasno objasnjen cilj slucaja upotrebe
  * prilozi

* Primer tekstualne dokumentacije slucaja upotrebe:

* **Naziv**: Prijavljivanje na konkurs
* **Akteri**: Kandidat koji se prijavljuje na konkurs za upis na
  fakultet, sluzbenik koji radi na evidentiranju kandidata.
* **Kratak opis**: Kandidat podnosi neophodna dokumenta i formulare
  na konkurs za upis na fakultet.
* **Tok dogadjaja**:
  * **Osnovni tok**:
    1. Kandidat donosi rukom popunjen obrazac P1 kao i sledeca 
       dokumenta:
       * fotokopiju izvoda iz matične knjige rođenih (original na 
         uvid), 
       * fotokopije svedočanstva sva četiri razreda srednje  
         škole (originali na uvid), 
       * fotokopiju svedočanstva o završenoj srednjoj školi       
         (original na uvid), 
       * potvrdu o uplati odgovarajućeg iznosa za prijavu. 
    2. Službenik proverava dokumenta i unosi podatke u sistem 
    3. Službenik štampa popunjene formulare 
    4. Kandidat potpisuje i predaje formulare 
    5. Službenik štampa i potpisuje obrazac P2 i uručuje kandidatu
  * **Alternativni tokovi**:
    1. Za strane državljane (osim za državljane BiH koji su 
       završili školu u RS), potrebna su i nostrifikovana školska  
       dokumenta ili potvrda o započetoj nostrifikaciji 
    2. Ako je kandidat položio prijemni ispit na drugom fakultetu,  
       potrebna je i potvrda o polozenom prijemnom ispitu na drugom
       fakultetu
    3. Ako je kandidat nosilac nagrada sa takmicenja koje mogu da
       doprinesu oslobadjanju od prijemnog ispita, popunjava i
       formular P3.
* **Preduslovi**: Kandidat je završio srednju školu i dobio 
  odgovarajuća dokumenta.
* **Postuslovi**: Kandidat je prijavljen i dobio je potvrdu koja
  sadrži redni broj prijave. 
* **Prilozi**: sadržaj i predložen izgled formulara P1, P2 i P3 
  * P1. Prijavni list sa ličnim podacima kandidata, podacima o mestu 
    rođenja, državljanstvu, roditeljima, prebivalištu, prethodno
    završenoj instituciji i studijskim programima koje kandidat želi 
    da upiše. 
  * P2. Identifikacioni list sa imenom, prezimenom i rednim brojem 
    prijave. 
  * P3. Formular za diplome koje kandidat prijavljuje i na osnovu 
    kojih želi da bude oslobođen od prijemnog ispita.

## Dijagram sekvence

* *Dijagram sekvence* opisuju tok odvijanja slucaja upotrebe.
* Vertikalna dimenzija predstavlja tok vremena, od vrha prema
  dnu dijagrama.
* Horizontalno se dijamgram deli na prostore koji odgovaraju 
  pojedinacnim objektima, i u svakoj koloni je u vrhu identifikacija
  objekta.
* Zatim se ispod crta isprekidana vertikalna linija koja
  predstavlja zivotni vek objekta.
* Na liniji se crtaju uski pravougaonici koji predstavljaju okvire
  aktivnosti, pocinje primanjem poruke, a zavrsava se kada se
  poruka obradi.

# Uvod u Projektovanje Softvera

# Obrasci za projektovanje



