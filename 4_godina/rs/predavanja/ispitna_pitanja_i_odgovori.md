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

50. Шта је УМЛ?

**Odgovor**: UML je ujedinjeni jezik za modelovanje.

51. Које (три) врсте дијаграма постоје у УМЛ-у? Објаснити.

**Odgovor**: 

* *Dijagram ponasanja*: dinamickom prirodom softverskog sistema;
* *Dijagram interakcije*: iterakcija izmedju razlicitih modela; 
* *Strukturni dijagram*: struktura softverskog sistema.

52. Навести структурне дијаграме УМЛ-а.

**Odgovor**: 

* Dijagram klasa
* Dijagram komponenti
* Dijagram objekata
* Dijagram profila
* Dijagram slozene strukture
* Dijagram isporucivanja
* Dijagram paketa

53. Која је улога и шта су основни елементи дијаграма класа?

**Odgovor**: Ilustruje strukturu modela, kao sto su klase, njigov
sadrzaj i medjusobnu povezanost. Sadrzi: naziv klasa, atribute klasa,
metode klasa, specijalizaciju i generalizaciju, odnose.

54. Како се представљају односи између класа на дијаграму класа? 
    Који односи постоје?

**Odgovor**: Asocijacija, Agregacija i Kompozicija koji se 
predstavljaju povezanim vrstama strelicama

55. Објаснити кардиналности односа на дијаграму класа – шта    
    представљају и како се означавају?

**Odgovor**: Kardinalnost odnosa predstavlja koliko instanci
asocijativne klase moze da sadrzi.

56. Које су врсте дијаграма класа и по чему се разликују?

**Odgovor**: *Dijagram modela domena* se bavi strukturom objekata,
dok se *dijagram interfejsa klase* se bavi ponasanjem objekata.

57. Која је улога и шта су основни елементи дијаграма компоненти?

**Odgovor**: Funkcionalna i fizicka komponenta softvera.

58. Која је улога и шта су основни елементи дијаграма објеката?

**Odgovor**: Naziv klase, naziv objekata, imena i vrednosti atributa
i odnose medju objektima u jednom trenutku vremena.

59. Која је улога и шта су основни елементи дијаграма испоручивања?

**Odgovor**: Fizicka arhitektura softverskog sistema.

60. Која је улога и шта су основни елементи дијаграма пакета?

**Odgovor**: Logicka dekompozicija u pakete. (`namespaces`)

61. Навести дијаграме понашања УМЛ-а.

**Odgovor**:

* Dijagram slucajeva upotrebe
* Dijagram aktivnosti
* Dijagram stanja
* Dijagram interakcije

62. Која је улога и шта су основни елементи дијаграма активности?

**Odgovor**: Poslovni procesi viseg nivoa, tokovi podatak, i slozene
logicke elemente sistema.

63. Која је улога и шта су основни елементи дијаграма стања?

**Odgovor**: Opisuje kako se stanje jednog objekta menja u zavisnosti
od interakcija u koje objekat ulazi.

64. Која је улога и шта су основни елементи дијаграма случајева 
    употребе?

**Odgovor**: Dijagram slucajeva upotrebe opisuje jednu funkcionalnu
celinu sistema. Osnovni elementi: *slucajevi upotrebe*, *akteri*, 
*njigovi medjusobni odnosi*.

65. Објаснити односе између случајева употребе на дијаграмима 
    случајева употребе.

**Odgovor**: 

* *include*: slucaj obuhvata citav slucaj prema kome ide strelica.
* *extends*: slucaj od koga ide strelica predstavlja opciono 
prosirenje drugog slucaja.

66. Шта обухвата опис једног случаја употребе?

**Odgovor**: Naziv, akteri, kratak opis, preduslovi, postpuslovi,
opis toka slucaja upotrebe, opis posebnih slucajeva, druge uml 
dijagrame.

67. Навести дијаграме интеракција УМЛ-а.

**Odgovor**: 

* Dijagram sekvence
* Dijagram komunikacije
* Dijagram vremena
* Dijagram interakcija

68. Која је улога и шта су основни елементи дијаграма комуникације?

**Odgovor**: Ilustruje objekte, njihove, medjusobne odnose i poruke 
koji rezmenjuju.

69. Која је улога и шта су основни елементи дијаграма интеракције?

**Odgovor**: Varijanta dijagrama aktivnosti, gde je akcenat na 
upravljanju procesima ili sistemom.

70. Која је улога и шта су основни елементи дијаграма секвенце?

**Odgovor**: Precizno opisuje tok odvijanja slucajeva upotrebe,
i jasno prepoznaje odgovornosti subjekta i objekta za pojedinacne
korake.


126. Шта је образац за пројектовање? Чему служи?

**Odgovor**: Obrazac za projektovanje predstavlja konceptualno resenje
neke klase problema, koje ide sa pratecom dokumentacijom. Sluzi za
resavanje nekog konkretnog problema, tako sto se pocetni problem apstrakuje
i iskoristi znanje iz konceptualnog resenja.

127. Који су основни елементи образаца за пројектовање? Објаснити их.

**Odgovor**:

* Ime
* Problem
* Resenje
* Posledice

128. Објаснити име, као елемент обрасца за пројектовање?

**Odogovor**: Ime obrasca za projektovanje sluzi da bi se u sto kracim 
terminima opisao problem, resenje i posledice. Koristi se za kataloge
obrazaca za projektovanje.

129. Објаснити проблем, као елемент обрасца за пројектовање?

**Odogovor**: Problem predstavlja opis apstrakcije neke klase problema.
Omogucava lako propoznavanje sa odredjenim problemom.


130. Објаснити решење, као елемент обрасца за пројектовање?

**Odogovor**: Resenje predstavlja detaljan apstraktni opis resenja problema.
Resenje ne sme biti konkretno vec mora biti sto je apstraktnije moguce, kako
bi moglo da se primeni u konkretnim problemima.

131. Објаснити последице, као елемент обрасца за пројектовање?

**Odogovor**: Posledice predstavljaju rezultate resenja. Sluze kao mera
pogodnosti odreddjenog obrasca za odredjeni problem.

132. Навести шта све обухвата опис једног обрасца за пројектовање? 

**Odgovor**: 

* Ime
* Alternativna imena
* Klasifikacija
* Namena
* Motivacija
* Primenjivost 
* Preduslov za primenu
* Logicka struktura resenja (UML dijagrami)
* Entiteti resenja (klase i objekti)
* Saradnja (dijagram sekvenci)
* Implementacija
* Primer koriscenja
* Primer koda
* Srodni obrasci

133. Како су класификовани обрасци за пројектовање? Навести по један пример од сваке врсте образаца.

**Odgovor**:

* Gradivni obrasci (Creational Patterns) (Factory Method)
* Strukturni obrasci (Structural Patterns) (Composite)
* Obrasci ponasanja (Behavioural Patterns) (Observer)

134. Објаснити намену градивних образаца за пројектовање.

**Odgovor**: Osnovan cilj gradivnih obrazaca je da olaksaju pravljenje novih
objekata. Oni apstrakuju proces pravljenja novih objekata iz interfejsa.

135. Навести бар четири градивна образаца за пројектовање.

**Odgovor**:

* Singleton
* Factory Method
* Abstract Factory
* Builder
* Prototype

136. Објаснити намену структурних образаца за пројектовање.

**Odgovor**: Osnovni cilj strukturnih obrazaca je da olaksaju ogranizaciju 
klasa i objekta u vece funkcionalne celine. Koriste nasledjivanje i 
hijerarhije klasa za povezivanje objekata i klasa.

137. Навести бар пет структурних образаца за пројектовање.

**Odgovor**::

* Composite
* Decorater
* Flyweight
* Facade
* Adapter
* Bridge
* Proxy

138. Објаснити намену образаца понашања.

**Odgovor**: Osnovni cilj obrazaca ponasanje je da olaksaju komunikaciju
izmedju objekata. 

139. Навести бар седам образаца понашања.

**Odgovor**: 

* Visitor
* Mediator
* Observer
* Template Method
* Strategy
* State
* Iterator
* Chain of Responsibility
* Command
* Memonto

140. Објаснити када се и како примењује образац Производни метод (Factory Method).

**Odgovor**: Pruza interfejs za pravljenje odredjenog objekta, ali prepusta
podklasi da odluci kada ce i kako napraviti taj objekat.
 
141. Скицирати дијаграм класа обрасца за пројектовање Производни метод (Factory Method).

**Odgovor**:

```
<<interface>>           Creator
   Product         + factoryMethod()
      ^            + operation()
      |                    ^
      |                    |
   AProduct <---------- ACreator
                   + factoryMetgod

```

142. Објаснити када се и како примењује образац Стратегија.

**Odgovor**: Definise okviran postupak nekog algoritma. Dok konkretni
koraci se prepustaju se konkretnim instancama

143. Скицирати дијаграм класа обрасца за пројектовање Стратегија.

**Odgovor**:

```
               <<interface>>
Context <>------ Strategy
                 +execute()
                  ^      ^
                  |      |
           StrategyA   StrategyB
           +execute()  +execute()
```
144. Објаснити када се и како примењује образац Декоратер.

**Odgovor**: Omogucavaju da se odredjene osobine i ponasanja definisu van
klase, tako da se odredjena komponenta dekorise njima. Smanjuju 
kombinatornu eksploziju u hijerarhiji.

145. Скицирати дијаграм класа обрасца за пројектовање Декоратер.

**Odgovor**:

```
<<interface>>
  Component   <----- AComponent
 +operation()   |   +operation()
      |         |
      |         ---  Decorator
      -----------<> +operation()
                        ^
                        |
                    ADecorator
                    -State
                    +operation()
                    +behavior()
```

146. Објаснити када се и како примењује образац Сложени објекат (Састав, Composite).

**Odgovor**: Povezuje vise objekata iste hijerarhije u jedan slozeni objekat.
Vodi racuna u njihovom pravljenju i brisanju.

147. Скицирати дијаграм класа обрасца за пројектовање Сложени објекат (Састав, Composite).

**Odgovor**:

```
    <<interface>>
      Component
    +operation()
    +add(c : Composite)    ---
    +remove(c : Composite)   |
    +get(i : int)            |
     ^        ^              ^
     |        |              v
    Leaf      |       Composite
+operation()  |     +operation()
              ----- +add(c : Composite)
                    +remove(c : Composite)
                    +get(i : int)
```

148. Објаснити када се и како примењује образац Уникат (Singleton).

**Odgovor**: Koristi se kada hocemo da imamo samo jedan jedini primerak 
neke klase.

149. Скицирати дијаграм класа обрасца за пројектовање Уникат (Singleton).

**Odgovor**:

```
        Singleton
    -static instance
    -data
    +static getInstance()
    +operation()
```

150. Објаснити када се и како примењује образац Посетилац (Visitor).

**Odgovor**: Razdvaja operacije nad nekim elementima od same implementacije
tih elemenata.

151. Скицирати дијаграм класа обрасца за пројектовање Посетилац (Visitor).

**Odgovor**:

```
          <<interface>>                     <<interface>>
            IVisitior                         IElement
    +visitElementA(a : ElementA)          +accept(v : Visitor)
    +visitElementB(b : ElementB)            ^               ^
                ^                           |               |
                |                      ElementA         ElementB
            Visitior              +accept(v : Visitor) +accept(v : Visitor)
    +visitElementA(a : ElementA)
    +visitElementB(b : ElementB)

```


152. Објаснити када се и како примењује образац Посматрач (Observer).

**Odgovor**: Posmatrac se primenjuje kada hocemo da pozovemo odgovarajuce
objekte koji posmatraju na neki dogadjaj posmatranog objekta. 

153. Скицирати дијаграм класа обрасца за пројектовање Посматрач (Observer).

**Odgovor**:
```
      <<interface>>               <<interface>>
        ISubject          notify   IObserver
    +attach(o : Observer) -------> +update()
    +detach(o : Observer)              ^
    +notify()                          |
            ^                          | 
            |        observe        Observer
        Subject <------------------ -state
        -state                      +update()
```

154. Објаснити када се и како примењује образац Апстрактна фабрика (Abstract Factory).

**Odgovor**: Primenjuje sa kada je potrebno napraviti familiju nekih objekata
u zavisnosti od platforme na kojoj se koristi program.

155. Скицирати дијаграм класа обрасца за пројектовање Апстрактна фабрика (Abstract Factory).

**Odgovor**:
```
      <<interface>>               <<interface>>
    IAbstractFactory                IProduct
    +createProductA()                  ^
    +createProductB()                  | 
            ^                          |
            |                          |
    AbstractFactory                 Product
    +createProductA()
    +createProductB()

```
