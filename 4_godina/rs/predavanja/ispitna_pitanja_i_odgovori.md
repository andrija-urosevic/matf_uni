# Razvoj Softvera: Ispitna Pitanja i Odgovori

1. Који од показивача `p1`, `p2` и `p3` није исправно дефинисан у 
   примеру?

```{c++}
int* p1,p2;
int* p3=(int*)1000; 
```

**Odgovor**: `p3` nije ispravno definisan.

2. У каквом су односу дужине низова s1 и s2 у примеру:

```{cpp}
char s1[] = "C++";
char s2[] = { 'C', '+', '+' };
```

**Odgovor**: 4:3

3. Шта ће исписати овај програм?

```{cpp}
int a = 1;
int* b=&a;
auto main(void) -> int
{
    *b = a + 1;
    *b = a + 1;
    std::cout << a << std::endl;

    return 0;
}
```

**Odgovor**: 3

4. Који концепти програмског језика C++ се употребљавају да би се 
   повећала (потенцијално поновљена) употребљивост написаног кода

**Odgovor**: Objektno-orijentisani koncepti sa velikom kohezijom
i malim uparivanjem.

5. Који је редослед уништавања објеката у примеру:

```{cpp}
int a(3);

auto main(void) -> int
{
    int* n = new int(10);
    int k(3);
    ...
    delete n;

    return 0;
}
```

**Odgovor**: Prvo se unistava `n`, zatim `k`, i na kraju `a`.

6. Да ли је нека (која?) од наредних линија кода неисправна?

```{cpp}
short* p = new short;
short* p = new short[900];
short* p = new short(900);
short** p = new short[900];
```

**Odgovor**: `short** p = new short[900];` je neispravna linija

7. Које операције класе Lista се извршавају у следећој наредби:

```{cpp}
Lista l2 = Lista();
```

**Odgovor**: Poziva se konstruktor klase `Lista`.

8. Колико пута се позива деструктор класе `А` у следећем програму?

```{cpp}
auto main(void) -> int 
{
    A a, b;
    A& c = a;
    A* p = new A();
    A* q = &b;

    return 0;
}
```

**Odgovor**: Poziva se dva puta. Za `a` i `b`, `c` je samo referenca 
na `a`, dok se `p` nalazi na hipu i potrebno je pozvati `delete p`, 
a `q` je pokazivac na `b`.

9. Шта су шаблони функција?

**Odgovor**: Sabloni funkcija su sredstvo za pisanje polimorfnih 
funkcija. Polimorfizam se ostvaruje apstrahovanjem nikih tipova
i/ili konstantni koje se pojavljuju u deklaraciji i implementaciji
funkcije.

10. Како се пишу и користе шаблони функција?

**Odgovor**: Sabloni funkcija pocinju sa *deklaracijom parametara
sablona*, koja se sastoji od kljucne reci `template`, iza koje se
u uglastim zagradama navode parametri sablona. Svaki parametar se
opisuje *vrstom* i *imenom*. Parametar sablona moze biti
*tipski parametar* (vrsta je kljucna rec `typename`) ili 
*konstantni parametar* (vrsta je tip konstante). Nakon toga sledi
deklaracija ili definicija funkcije u koje se mogu koristiti
imena kao parametrizovani tipovi. Zamenjivanjem sablona konkretnim
tipovima i konstantama naziva se *instanciranje sablona*. Postoje
dve mogucnosti za instanciranje sablona: *eksplicitnim vezivanjem
parametara* i *implicnitnim vezivanjem parametara*. Ekspicitno
vezivanje podrazumeva da pri pozivu funkcije navedu vrednosti
parametara, dok kod implicitnog vezivanja prevodilac sam prepoznaje
tipove, ako ne postoji jednoznacno resenje prijavljuje gresku.

11. Написати шаблон функције која рачуна средњу вредност два броја 
    за било који нумерички тип.

**Odgovor**:

```{cpp}
template<typename T>
inline T arithmetic_mean(const T& a, const T& b)
{
    return (a + b) / 2;
}
```

12. Шта су шаблони класа?

**Odgovor**: Sabloni klasa predstavljaju stedstvo za pisanje 
polimofrnih tipova podataka. Polimorfizam se ostvaruje apstrahovanje
nekih tipova i/ili konstanti u deklaraciji i definiciji klase.

13. Како се преводе шаблони класа?

**Odgovor**: Proces prevodjenja se odvija tako da se u prvom prolazku
ispita da li postoji neka greska u sintaksi klase. Kada se 
inicijalizuje sablon klase prevodilac ponovo prevodi strukturu klase 
i uocava eventualne probleme u strukturi. Ali prevodjenje instanci
metoda se odlaze sve do njihovog koriscenja.

14. Шта је неопходан услов да би се позиви неког метода динамички 
    везивали? Шта је довољан услов?

**Odgovor**: Potrebno je koristiti virtualne funkcije.

15. Шта је виртуална функција?

**Odgovor**: Virtualna funkcija je member funkcija koju ocekujemo
da ce biti redefinisana u nasledjenoj klasi. Kada se pristupa 
nasledjenom objektu preko pokazivaca i reference baznog objekta,
poziv virtualne funkcije ce izvrsiti izvedenu verziju te funkcije.
Virtualne funkcije se deklarisu sa kljucnom reci `virtual`.

16. Шта је чисто виртуална функција?

**Odgovor**: Cisto virtualna funkcija je virtualna funkcija bazne
klase koja se mora ponovno implementirati u svim izvedenim klasama.
Oznacava se tako sto se doda *cisti* specifikator `= 0` na kraju 
deklaracije.

17. Шта је апстрактна класа?

**Odgovor**: Apstraktna klasa se ponasa kao generalni koncept koji
specificne klase nasledjuju. Ne moze se napraviti objekat apstraktne
klase, ali moze se koristiti pokazivac ili referenca apstraktne 
klase. Apstraktna klasa mora deklarisati bar jednu cisto virtualnu 
funkciju.

18. Шта су уметнуте (inline) функције? Како се пишу?

**Odgovor**: Umetnute (inline) funkcije se ne prevode vec se njihova
definicija umetne pri svakom pozicu. Pisu se tako sto im se doda
kljucna rec `inline` u deklaraciji.

19. Шта су уметнути (inline) методи? Како се пишу?

**Odgovor**: Umetnuti (inline) metodi su metodi koji se definisu
unutar deklaracije klase. Pisu se tako sto im se doda kljucna rec
`inline` u deklaraciji (ekspicitno) ili tako sto se se pored
deklaracije odmah i definisu (implicitno).

20. Која су основна мерила неуспеха при развоју софтвера? Објаснити 
    свако укратко.

**Odgovor**:

* Ulozena sredstva: Koliko je novca potroseno.
* Izgubljeno vremo: Koliko je vremena potroseno.
* Posledice po citav poslovni sistem: Koliko ce poslovni sistem 
  izgubiti zbog neuspeha pri razvoju softvera.

21. Које су основне врсте неуспеха при развоју софтвера? Објаснити 
    сваку укратко.

**Odgovor**:

* Prekoracenje troskova: Planirano je x\$, potrebno je (x + y)\$
* Prekoracenje vremenskih rokova: Povlaci vece troskove
* Rezultat nije upotrebljiv: Neispravno funkcionise ili je 
  neupotrebljiv u realnim problemima 
* Odustajanje od projekta: Nastaje zbog nekog od prethodnih razloga
* Katastrofale greske: Bagovi koji ne mogu da se otklone.

22. Шта је неупотребљив резултат? Који су аспекти неупотребљивости?
Објаснити.

**Odgovor**: Neupotrebljiv rezultat predstavlja softver koji ne 
funkcionise ili ne zadovoljava realne probleme. Aspekti 
neupotrebljivosti: (1) Neupotrebljiv korisnicki interfejs, 
(2) Procedura koriscenja nije ostvarena/dobra u realnim uslovima.

23. Који су најчешћи узроци неупотребљивости резултата развоја 
    софтвера? Објаснити укратко.

**Odgovor**: 

* Problem na strani klijenta: Klijent ne zna sta hoce, ime nerealne 
  uslove, manjak sredstava...
* Problem na strani razvijalaca: Slabo vodjenje projekta, losa
  procena potrebnih resursa, nove tehnologije...
* Visestrani problemi: Losa komunikacije, lose definisani zahtevi.

24. На којим странама се налазе проблеми при развоју софтвера? 
    Објаснити укратко и навести по један пример.

**Odgovor**: Odgovoreno gore.

25. Који су најчешћи проблеми на страни заинтересованих лица    
    (улагача) при развоју софтвера?
    Објаснити укратко.

**Odgovor**: Odgovoreno gore.

26. Који су најчешћи проблеми на страни развијаоца при развоју    
    софтвера? Објаснити укратко.

**Odgovor**: Odgovoreno gore.

27. Који су најчешћи проблеми који се односе на обе стране у развоју 
    софтвера (улагачи и развојаоци)? Објаснити укратко.

**Odgovor**: Odgovoreno gore.

28. Објаснити како приступи планирању могу довести до проблема.

**Odgovor**: Moze docei do nedovoljnog planiranja ili do preteranog
planiranja.

29. Шта је управљање ризицима?

**Odgovor**: Proces preoznavanja, pocenjivanja i kontrolisanja svega
sto moze da krene naopako pri razvoju softvera.

30. Који су основни узроци ризика у развоју софтвера? Навести бар 7.

**Odgovor**: 
* manjak osoblja
* nerealni rokovi i budzet
* razvoj potrebnih funkcija
* razvoj pogresnog interfejsa
* preterivanje
* neprikidni niz izmena u zahtevima
* slabnosti eksterno realizovanih poslova
* slabosti u eksterno nabavljenim komponentama
* slabe performanse u realnom radu
* rad na granicama racunarskih nauka

31. Који су најважнији савремени концепти развоја који су настали из 
    потребе за смањивањем ризика у развојном процесу?

**Odgovor**:

* Inkrementalni razvoj
* Odredjivanje koraka prema rokovima
* Pojacanje komunikacija medju subjektima
* Davanje prednosti objektima u odnosu na proces
* Prevljenje prototipova

32. Објаснити концепт инкременталног развоја?

**Odgovor**: Veliki i slozeni posao delima na male i jednostavne 
celine koje nadogradjujemo kroz inkrementalne faze.

33. Објаснити концепт одређивања корака према роковима?

**Odgovor**: Za svaki korak se odredi budzet i rokovi, te se onda
oni ispunjavaju.

34. Објаснити концепт појачане комуникације међу субјектима?

**Odgovor**: U planiranju se razmatraju sve vreste subjekata u sto
vecem broju.

35. Објаснити концепт давања предности објектима у односу на процесе?

**Odgovor**: U sredini paznje se pri razvoju stavljaju objekti, a
ne procesi.

36. Објаснити концепт прављења прототипова?

**Odgovor**: U okviru analize problema se pravi prototip koji odrazava nacin funkcionisanja i upotrebe softvera.

37. У којим околностима су настале објектно оријентисане развојне 
    методологије?

**Odgovor**: 

* Postojanje metodologija koje striktno pripisuje analizu i 
  opisivanje procesa
* Potreba za strktuiranim opisivanjem podataka
* Potreba za opisivanjem entiteta koji menja stanja.
* Podizanje nivoa apstraksicje
* Programiranje upravljano dogadjajima
* Graficki korisnicki interfejs
* Modularnost softvera
* Skracivanje razvojnog ciklusa
* Visestruka upotrebljivost softvera

38. Објаснити основне концепте приступања објектно оријентисаних 
    развојних методологија проблему развоја.

**Odgovor**: 

* Srediste paznje se stavlja na objekte, a ne na proces.
* Skracivanjem trajanja razvojnog ciklusa.
* Pojacana komunikacija medju subjektima u svim fazama razvoja.

39. Шта је објекат? Објаснити својим речима и навести једну од познатих дефиниција.

**Odgovor**: Objekat je primerak neke klase. Svaki objekat moze da
sadrzi svoje stanje i ponasanje, koje se definise u klasi.

40. Шта је класа? Атрибут? Метод?

**Odgovor**: *Klasa* je skup svih objekata koji imaju zajednicka
(1) atribute i (2) metode. *Atribut* je odgovarajuce polje koje ima 
ime i tip. *Metod* je odgovarajuce ponasaljen koje ima ime, 
argumente i povratnu vrednost.

41. Који су основни концепти на којима почивају технике објектно оријентисаних методологија?

**Odgovor**:

* Enkapsulacije
* Interfejs
* Poliomrfizam
* Nasledjivanje i odgovarajuci odnosu

42. Објаснити концепт енкапсулације.

**Odgovor**: Enkapsulacija je ideja da je strukturu objekta zanima
samo taj objekat.

43. Објаснити концепт интерфејса.

**Odgovor**: Interfejs je ideja da klasa spoljasnjim korisnicima
omogucava samo odredjeni skup ponasanja i tako komunicira sa 
objektom.

44. Објаснити концепт полиморфизма.

**Odgovor**: Polimorfizam je ideja da jednom napisan kod moze da
se koristi vise razlicitih vrsta objekata.

45. Објаснити концепт наслеђивања и одговарајуће односе.

**Odgovor**: Nasledjivanje klase je ekvivalentno relaciji `jeste`
koja se definise kao: (1) Klasa `A` `jeste` klasa `B` akko svaki 
objekat klasa `A` ima sve osobine koji imaju i objekti klase `B`.

46. Кроз које фазе је прошао развој ОО методологија?

**Odgovor**:

* Pocetni koraci
* Oblikovanje UML-a
* Post-UML koraci

47. Које су карактериситике прве фазе развоја ОО методологија?

**Odgovor**: Veliki broj razlicitih notacija i metodologija.
Previse siroka i nije bilo kompletana.

48. Које су карактериситике друге фазе развоја ОО методологија?

**Odgovor**: Pokusaj ujednacenja notacije, akcenat na notaciji.

49. Које су карактериситике треће фазе развоја ОО методологија?

**Odgovor**: Ujednacena notacija, siroko shvatanje procesa razvoja,
agilne metodologije, potpuno posvecivanje metodologijama...

