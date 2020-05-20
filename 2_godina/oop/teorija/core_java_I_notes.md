# Uvod u Javu

* Java Buzzwords:
  1. Jednostavan
  2. Objektno orijentisan
  3. Distributivan
  4. Robustan
  5. Siguran
  6. Arhitektnosko neutralan
  7. Portabilan
  8. Interpretiran
  9. Visoke performanse
  10. Visenitan
  10. Dinamican

# Java Programsko Okruzenje

# Fundamentalne Strukture u Javi

## Jednostavni Java Program

```java
package org;

public class SimpleProgram {

    public static void main (String[] args) {
        System.out.println("Hello, World");
    }
}
```

* Case Sensitive
* `public` je access modifier
* `class` sve u javi zivi u klasi
* Imena lakse pocinju velikim slovom, dok ostale reci u imenu takodje pocinju
  velikim slovom --- CamelCase.
* Ime kalse mora da se zove isto kao i ime fajla
  * Pored toga ima fajla ima ekstenziju `.java`.
* Nakon kompajliranje dobija se bajtkod sa ekstenzijom `.class`.
* `{}` odvajaju blokove
* `objekat.metod(parametri)` standardan poziv metode u javi

## Komentari

* `//` se koristi za pocetak komentara koji traje do kraja linije
* `/*` i `*/` se koriste za pocetak i kraj bloka komentara
* `/**` i `*/` se koristi za pocetak i kraj bloka komentara koji
  se koristi za generisanje dokumentacije automacki.

## Tipovi Podataka

* Java je *strogo tipiziran jezik*.
* Postoji 8 *primitivnih tipova* u Javi.

### Celobrojni tipovi

* `int` --- 4 bajta
* `short` --- 2 bajta
* `long` --- 8 bajtova
* `byte` --- 1 bajt
* Long imaju sufik `L` (`4000000000L`)
* Heksadecimalni brojevi imaju prefix `0x` ili `0X` (`0xCAFE`)
* Oktalni imaju prefix `0` (010)
* Binarni imaju prefix `0b` ili `0B` (`0b1001`)
* Moguce je dodavanje `_` za bolju citljivost (`0b1111_1010_1001_0000`)

### Brojevi u Pokretnom zarezu

* `float` --- 4 bajta
* `double` --- 8 bajta
* float imaju sufiks `f` ili `F` (`3.14F`)
* brojevi bez sufiksa podrazumevaju se kao `double`
  * ili mogu imati `d` ili `D` (`3.14D`)
* Zasnovani su na IEEE-754
* Pozitivna beskonacnost
* Negativna beskonacnost
* NaN (Not a Number)

### Char tip

* `char` se nalazi u zatvorenim apostrofima (`'A'`) dok se pod 
  navodinicima nalazi `String` (`"A"`).
* Mogu se predstaviti heksadecimalnim vrednostima od `\u0000` do `\uFFFF`.
  * Predstavljaju unicode karaktere.

### Unicode i char tip

* Unicode je dizajniran da resi porblem razlicitog kordiranja slova u 
  razlicitim jezicima.
* Fiksirana 2-bajta su bila dovoljna da se koridaju sva slova iz svih
  jezika jedinstveno, ili su bar tako svi mislili.
  * Na pocetku sa prvom verzijom ostalo je oko pola praznih mesta, ali zbog
    jezika kao sto su kineski, japanski i koreanski popunili su i ostatak
    masta tako da nisu mogli da smeste znakove.
* *Code point* je kodirana vrednost koja je povezana sa karakterom u 
* Prva je klasicna koja sadrzi karaktere od `U+0000` do `U+FFFF`.
* Ostalih 16 sadrze supplementary characters i kodiraju se `U+10000` do
  `U+10FFFF`
* UTF-16 enkodiranje predstavlja sve Unicode code points u promenljivoj 
  duzini koda. 
  * Karakteri koji su u prvoj klasicnoj grupi se predstavljaju kao 16-bitne
    vrednosti, nazvane *code units*.
  * Supplementary characters su enkodiranai kao uzastopni parovi code units.
* U Javi `char` tip opisuje `code unit` u UTF-16 enkodiranju.

### Boolean tip

* `boolean` ima samo dve vrednosti, `false` i `true`.
  * Ne moze se konvertovati izmedju `int` i `boolean`.

## Promenljive

* Svaka promenljiva u javi ima svoj tip.
* Deklaracija:
  * `<type> varName;` (na primer `double salary`)
* Ime promenljive `varName` mora poceti slovom i mora biti sekvenca 
  slova i/ili brojeva.
  * Slova: `'A'-'Z', 'a'-'z', '_', '$'` ili bilo koji Unicode karakter koji
    predstavlja slovo u nekom jeziku.
  * Broj: `'0'-'9'` ili  bilo koji Unicode karakter koji predstavlja broj
    u nekom jeziku.
* Ime promenljive ne sme biti neka od kljucnih reci.

### Inicijalizacija promenljivih

* Pre koriscenja deklarisane promenljive ona mora biti inicijalizovana.
  * Deklaracija pa inicijalizacija:
    ```java
    int vacationDays;
    vacationDays = 12;
    ```
  * Deklaracija i inicijalizacija:
    ```java
    int vacationDays = 12;
    ```
* Deklaracija ili inicijalizacija se mogu naci bilo gde u kodu.

### Konstante

* U javi se koristi kljucna rec `final` da konstante.
```java
final double CM_PER_INCH = 2.54;
```
* *Klasne konstante* imaju dodato `static` i nalaze se u klasi izvan
  svih funcija kako bi se mogle referisati u svakoj funkciji:
```java
static final double CM_PER_INCH = 2.54;
```

## Operatori

* Uobicajni aritmeticki operatori `+, -, *, /` se koriste u Javi za 
  sabiranje, oduzimanje, mnozenje i deljenje.
  * `/` se razlikuje kada delji celobrojne tipove i tipove sa pokretnim 
    zarezom.
  * `%` ostatak pri deljenju celobrojnih tipova
  * Deljenje nulom kod celobrojnih tipova uzrokuje izuzetke, dok kod
    tipova sa pokretnim zarezom dobijamo beskonacno ili NaN kao rezultat.

### Matematicke funcije i konstante

* `Math` klasa sadrzi veliki broj matematickih funkcija.
```java
double x = 4;
dobule y = Math.sqrt(x);
double z = Math.pow(x, 4);
```
* Trigonometrijske funkcija:
```java
Math.sin
Math.cos
Math.tan
Math.atan
Math.atan2
```
* Eksponencijalne i logaritamske funkcije:
```java
Math.exp
Math.log
Math.log10
```
* Konstante
```java
Math.PI
Math.E
```

### Konverzija izmedju numberickih tipova

```
                   char
                    |
                    v
byte --> short --> int  -->  long
                    |  \   /  |
                    |   ---   |
                    v _/   \_ v
                  float --> double
```

* Kada se dve vrednosti razlicitog tipa kombinuju sa binarnom operacijom,
  uvek se prvo vrednosti prebace u isti tip po gore navedenom pravilu, pa
  se na njih primeni operacija. 

### Kastovanje

* Po nekada zelimo da na primer `double` posmatramo kao `int`.
* To je moguce ali naravno informacija moze biti izgubljena.
* Tu operaciju nazivamo *kastovanje*.
```java
double x = 9.997;
int nx = (int) x; // nx = 9
int mx = (int) Math.round(x); // nx = 10 Math.round(x) vraca long 
                              // te je potrebno kastovanje
```

### Kombinovanje Dodele sa Operatorima

```java
// Sledece dve linije su ekvivalentne
x += 4;
x = x + 4;
```

### Inkrementalni i Dekrementalni Operatori

* Slede korake jezika C i C++.
* `n++; ++n; n--; --n;`

### Relacioni i boolean Operatori

* Jednakost: `3 == 7` dobijamo `false`.
* Nejednakost: `3 != 7` dobijamo `true`.
* Slicno kao u C-u imamo `<, >, <=, >=`.
* Takodje ima dve binarne logicke operacije *i* i *ili*: `&&` i `||`
  * Ove logicke operacije podrzavaju lenjo izracunavanje.
* Ima i jednu unarnu logicku operaciju negacije: `!`
* Takodje podrzava i jednu ternarnu operaciju `?:`
  * `condition ? expression1 : expression2;`
  * Izracunava `expression1` ako je zadovoljen `condition`, u suprotnom
    izracunava `expression2`.

### Bitovski operatori

* Bitovsko *i*, *ili*, *xor* i *ne*: `&, |, ^, ~`.
* Softovanje udesno i ulevo: `>>, <<`
* Takodje siftovanje udesno tako sto popunjava pocetne bitove nulama: `>>>`.

### Zagrade i Operatori: Hijerarhija

* Klasicno kao i u C-u sem sto java nema `,` operator.

### Enumerisani tipovi

* Ponekada zelimo da promenljiva drzi samo neki skup mogucih promenljivih.
* Enumerisani tip ima skonacna broj imenovanmih vrednosti:
```java
enum Size { SMALL, MEDIUM, LARGE, EXTRA_LARGE };
Size s = Size.MEDIUM;
```

## String

* Java `String` je sekvenca Unicode karaktera.
* Ne postoji predefinisani `String` tip, vec je on u formi klase.
* Svaki navedeni string je instanca klase `String`.
```java
String e = "";
String greeting = "Hello";
```

### Podstring

```java
String greeting = "Hello";
String s = greeting.substring(0, 3); // s = "Hel"
```

### Konkatinacija ili Nadovezivanje

```java
String expletive = "Explective";
String PG13 = "deleted";
String message = expletive + PG13;

int age = 13;
String ratioin = "PG" + age;

String all = String.join(" / ", "S", "M", "L", "XL");
// all = "S / M / L / XL"
```

### Stringovi su Imutabilni

* Klasa `String` nema metod za menjanje karaktera u postojacem stringu.
* Kako nije moguce menjanje induvidulanih karaktera u Java strinug, 
  dokumentacija referisa objekte klase `String` kao *imutabilne*.
  * Kako nije moguce menjanje samo stringova moguce je menjanje sadrzaja 
    datog objekta da referisa na neki drugi string.
* Ovo ima prednosti i mana. Naime, nije efikasno da generisemo novi string
  ako hocemo da promenimo samo dva zadnja karaktera u postojacem stringu, ali
  kompajler moze da ih uredi tako da neki od njih budu deljenji.
  * Svi stringovi se nalaze u bazenu. I String promenljive pokazuju na 
    lokaciju nekih od stringova u bazenu. Ako hocemo da imamo kopiju
    neke String promenljive dovoljno je kopirati njenu lokaciju, a ne i sam
    string i time povecati velicinu bazena.

### Testiranje Jednakosti Stringova

* `s.equals(t)`: vraca `true` ako su `s` i `t` jednaki, u suprotnom
  vraca `false`.
* `"Hello".equalsIgnoreCase("hello")` vraca `true`.
* `s == t` za ispitivanje daje nepredvidive rezultate 

### Prazni i Null Stringovi

* Prazan string `""` je duzine 0.
  * Testiranje da li je string prazan: `if (str.length() == 0)` ili 
    `if(str.equals(""))`
* `String` promenljiva takodje moze da drzi posebnu vrednosti `null`.
  * `null` pokazuje da ne postoji objekat koji je povezan sa promenljivom.
  * Testiranje da li je string `null`: `if(str == null)`
* Testiranje da li je string `null` ili prazan: 
  `if(str != null && str.lenght() == 0)`

### Code Points i Code Units

* Java stringovi su implementirani kao sekvenca `char` vrednosti.
* `str.lenght()` vraca broj code units potrebnih za dati string `str` u 
  UTF-16 enkodiranju.
* Za pravu duzinu koristi se `str.codePointCount(0, str.lenght())`
* `str.charAt(n)` vraca code unit na pozociji `n`, gde je `n` izmedju 
  0 i `str.length() - 1`.
* `str.codePointAt(str.offsetByCodePoints(0, i))` vraca `i`ti code point.

### String API

* Klasa `String` sadrzi vise od 50 metoda.
  * `char charAt(int index)`
  * `int codePointAt(int index)`
  * `int offsetByCodePoints(int startIndex, int cpCount)`
  * `int compareTo(String other)`
  * `IntStream codePoints()`
  * `new String(int[] codePoints, int offset, int count)`
  * `boolean equals(Object other)`
  * `boolean equalsIgnoreCase(String other)`
  * `boolean startsWith(String prefix)`
  * `boolean endsWith(String suffix)`
  * `int indexOf(String str)`
  * `int idnexOf(String str, int fromIndex)`
  * `int indexOf(int cp)`
  * `int indexOf(int cp, int fromIndex)`
  * `int lastIndexOf(String str)`
  * `int lastIndexOf(String str, int fromIndex)`
  * `int lastIndexOf(int cp)`
  * `int lastIndexOf(int cp, int fromIndex)`
  * `int length()`
  * `int codePointCount(inst StartIndex, int endIndex)`
  * `String replace(CharSequence oldString, CharSequence newString)`
  * `String substring(int beginIndex)`
  * `String substring(int beginIndex, int endIndex)`
  * `String toLowerCase()`
  * `String toUpperCase()`
  * `String trim()`
  * `String join(CharSequence delimiter, CharSequence... elements)`

### Building Strings

* Ponekada je potrebno graditi string iz kracih stringova.
  * Nefikasno je vrsiti konkatonaciju jer svaka konkatonacija stvara novi
    `String` objekat.
  * `StringBuilder` resava ovaj problem
```java
StringBuilder sb = new StringBuilder();
sb.append(ch);  // appends char
sb.append(str); // appends string
String s = sb.toString();
```
* `StringBuilder()` 
* `int length()`
* `StringBuilder append(String str)`
* `StringBuilder append(char c)`
* `StringBuilder appendCodePoint(int cp)`
* `void setCharAt(int i, char c)`
* `StringBuilder insert(int offset, String str)`
* `StringBuilder delete(int startIndex, int endIndex)`
* `String toString()`

## Ulaz i Izlaz

### Citanje sa Ulaza

```java
Scanner in = new Scanner(System.in);
String name = in.nextLine();  // cita celu liniju (string)
String firstName = in.next(); // cita sledecu rec (string)
int age = in.nextInt();       // cita sledeci int
int hight = in.nextDouble();  // cita sledeci double
in.close();         
```

### Formatiranje Izlaza

```java
double x = 1000.0 / 3.0;
System.out.print(x); // stampa 333.33333335
System.out.printf("%8.2f", x) // stampa 3333.33 (8 polja sa preciznoscu 2)
```
* *Format specifiers* pocinju sa `%` i zavrsavaju se sa 
  *conversion character*. (na primer `%f`- flaot, `%s` - string)
* Moguce je specificirati *flags* koji kontrolisu formatiranje izlaza.
```
format-specifier:

--->%-------------------------------------------------------------------->conversion-->
      |                 ^ ^        | |          ^ | |                  ^  character  ^
      '-->argument-->$--' '--flag--' '-->width--' | '-->.-->precision--'             |
           index                                  |                                  |
                                                  '----->t------->conversion---------'
                                                                  character
```

### Ulaz i Izlaz sa fajlovima

* Za citanje iz fajla: 
```java
Scanner in = new Scanner(Paths.get("myfile.txt"), "UTF-8");
```
* Za pisanje u fajl:
```java
PrintWriter out = new PrintWriter("myfile.txt", "UTF-8");
```
* Kod citanja iz fajlova ako fajl ne postoji na toj putanji dolazi
  do *exception*. Java koristi drugacije nacine za obradjivanje expections. 

## Controla Toka

### Blokovi

* Blokovi sadrze nekoliko Java naredbi, koje objedinjuju par 
  viticastih zagrada `{ }`.
* Blokovi se mogu ugnjezditi u druge blokove.
```java
public static void main(String[] args)
{
   int n;
   . . .
   {
      int k;
      int n; // greska! ne moze se redefinisati u unutrasnjem bloku
      . . .
   } // k je definisano samo dovde
}
```

### Uslovne naredbe

```java
if (condition) statement

if (condition) {
    statement1
    statement2
    ...
}

if (condition) statement1 else statement2

if (condition1) 
    statement1 
else if (condition2)
    statement2
...
else if (conditionm)
    statementm
else
    statementm+1
    
```

### Petlje

```java
while (condition) statement

do statement while (condition);
```

### Determinisane Petlje

```java
for (initStatement; condition; ithStatement)
    statement
```

### Switch naredba

```java
switch (label) {
    case 1:
        ...
        break;
    case 2:
        ...
        break;
    case 3:
        ...
        break;
    case 4:
        ...
        break;
    defalut:
        ...
        break;
}
```
* `label` moze da bude:
  * `char, byte, short, int`
  * enumerisana konstanta
  * `String`

### Naredba za Prestanak Kontrole Toka

* `goto` je rezervisana rec ali ne sluzi ni cemu.
* neoznaceni `break` izlazi iz petlje.
* onazneni `break` izlazi iz petlje do oznacenog mesta.
```java
read_data:
while (...) {
    for (...) {
        n = in.nextInt();
        if (n < 0) {
            break read_data;
        }
    }
}

// Ovde se nastavlja izvrsavanje nakod izlazenje
...
```
* `continue` prestaje sa izvrsavanjem bloka i vraca se na pocetak petlje.

## Veliki Brojevi

* `BigInteger` i `BigDecimal` su klase za predstavljanje proizvoljno
  velikih sekvenca brojeva.
```java
BigInteger a = BigInteger.valueOf(100);
BigInteger b = BigInteger.valueOf(1000);
BigInteger c = a.add(b);                                 // c = a + b
BigInteger d = c.multiply(b.add(BigInteger.valueOf(2))); // d = c * (b + 2)
```
* `BigInteger add(BigInteger other)`
* `BigInteger subtract(BigInteger other)`
* `BigInteger multiply(BigInteger other)`
* `BigInteger devide(BigInteger other)`
* `BigInteger mod(BigInteger other)`
* `int compareTo(BigInteger other)`
* `static BigInteger valuOf(long x)`

## Nizovi

* Niz je struktura podataka koja cuva kolekciju vrednosti istog tipa.
* Moguce je pristupati svakoj vrednosti preko *index*a.
  * Ako je `a` niz onda je `a[i]` `i`ti element tog niza.
* Deklaracija:
  * `<type>[] arrayName;` 
    * na primer: `int[] a;`
* Deklaracija i Inicijalizacija
  * `<tipe>[] arrayName = new <tipe>[numberOfElements];`
    * na primer: `int[] a = new int[100];`
* Kada se kreira novi niz brojeva, svi elementi su inicijalizovani na 0,
  dok kada se kreira niz tipa `boolean` onda se incijalizije sa `false`.
* Niz objekta se inicijalizuje sa specijalnom vrednoscu `null`.
* `array.length` daje broj elemenata u nizu.
* Jednom kreiran niz neke velicine, nije moguce menjati tu velicinu.
  * Ako je potrebno stalno povecanje niza obicno se koristi `array list`.

### For each Petlja

```java
for (variable : collection) statement
```
* `collection` izraz mora da bude niz ili objekat koji implementira
  `Iterable` interfejs, kao sto je na primer `ArrayList`.
```java
// For each petlja
for (int element : a) {
    System.out.println(element);
}
// Tradicionalna petlja
for (int i = 0; i < a.length; i++) {
    System.out.println(a[i]);
}
```

### Inicijalizatori Niza i Anonimni Nizovi

```java
int[] smallPrimes = { 2, 3, 5, 7, 11, 13 }; 
new int[] {17, 19, 23, 29, 31, 37} // Anonimni niz
```
* Anonimni nizovi se mogu koristiti kod ponovne inicijalizacije nekog niza
  kako se ne bi kreirao novi niz.
```java
smallPrimes = new int[] {17, 19, 23, 29, 31, 37}; 
// je krace od
int[] tmp = {17, 19, 23, 29, 31, 37};
smallPrimes = tmp;
```

### Kopiranje Nizova

* Moguce je kopiranje jedne promenljive niza u drugu, ali onda obe
  promenljive referisu na isti niz:
```java
int[] luckyNumbers = smallPrimes;
luckyNumbers[5] = 12; // sada je i smallPrimes[5] = 12

// Kopiranje vrednosti u novi niz:
int[] copiedLuckyNumbers = Array.copyOf(luckyNumbers, luckyNumbers.length);
```
* `copyOf` metod ima dva argumenta prvi je sam niz iz koga kopiramo, dok
  je drugi duzina novog niza, ako je veca od originalnog, ostale vrednosti
  se postavljaju na `0`, `false`, ili `null`.

### Parametri Komandene Linije

* Svaki Java program ima `main` metodu sa `String[] args` parametrom.
* Ovi parametri argumente koji su specifikovani u komandnoj liniji prilikom
  pokretanja programa.
```java
public static void main(String[] args) {
    if (args.lenght == 0 || args[0].equals("-h")) {
        System.out.print("Hello, ");
    } else if (args[0].equals("-g")) {
        System.out.print("Goodbye, ");
    }

    for (int i = 1; i < args.length; i++) {
        System.out.print(" " + args[i]);
    }
    System.out.println("!");
}


java Main -h nice world!
out: Hello, nice world!
```

### Sortiranje Niza

```java
int[] a = new int[1000];
...
Arrays.sort(a);
```
* `sort()` metod je Quick Sort koji je podesen kako bi bio optimalan
  na razlicite setove podataka.
* `static String toString(type[] a)`
* `static type[] copyOf(type[] a, int length)`
* `static type[] copyOfRange(type[] a, int start, int end)`
* `static void sort(type[] a)`
* `static int binarySearch(type[] a, type v)`
* `static int binarySearch(type[] a, int start, int end, type v)`
* `static void fill(type[] a, type v)`
* `static boolean equals(type[] a, type[] b)`

### Visedimenzionalni Nizovi

* Multidimenzionalni nizovi koriste vise od jednog indeksa za pristup
  elementima niza.
* Deklaracija:
  * `type[][] arrName;`
* Inicijalizacije:
  * `arrName = new type[N][N];`
* Inicijalizacija sa poznatim vrednostima:
  * ```java
    int[][] arr = {
        {1, 2, 3, 4},
        {2, 2, 2, 2},
        {2, 2, 2, 2},
        {4, 3, 2, 1},
    };
    ```
* Pristup individulanom elemntu:
  * `arrName[i][j]`
* Menjanje individualnog elemnta:
  * `arrName[i][j] = v;`

### Iseckani Nizovi

* U javi zapravo ne postoje vise-dimenzionalni nizovi.
* Vise-dimenzionalni nizovi su samo nizovi nizova.
* Zbog toga je moguce imati nesto ovako:
```
1
1  1
1  2  1
1  3  3  1
1  4  6  4  1
1  5 10 10  5  1
1  6 15 20 15  6  1
```
```java
int[][] binomial = new int[NMAX + 1][];
for (int n = 0; n <= NMAX; n++) {
    binomial[n] = new int[n + 1];
}

binomial[0][0] = 1;
for (int n = 1; n < binomial.length; n++) {
    binomial[n][0] = 1;
    for (int k = 1; k < binomial[n].length - 1; k++) {
        binomial[n][k] = binomial[n - 1][k] + binomial[n - 1][k - 1];
    }
    binomial[n][binomial[n].length - 1] = 1;
}

```
    
# Objekti i Klase

## Uvod u Objektno-Orijentisano Programiranje

* Objektno-Orijentisan program se sastoji od objekata.
  * Svaki objekta ima specificne funkcionalnosti.
  * Mnogi objekti su preuzeti iz biblioteka, drugi moraju biti napravljeni.
  * Sve dok neki objekat zadovoljava specifikacije, ne zanima nas 
    implmentacija.
* Tradicionalno proceduralno programiranje se zasniva na dizajniranju nekog 
  skupa procedura za resavanje probleme, a nakon toga se pronalaze nacini sa 
  skladno smestanje podataka.
* Objektno-Orijentisano programiranje okrece ovaj proces:
  1. Smestimo prvo podatke
  2. Pravimo algoritme za operisanje nad tip podacima

### Klase

* *Klasa* je blueprint sa kojim se prave objekti.
  * Kada konstruisemo objekat iz klase, kazemo da smo stvorili *instancu* 
    klase.
* Sav kod u Javi se nalazi u klasi.
* *Enkapsulacija* je kljucan koncept, koji spaja podatke i ponasanja u jedan
  paket, i skrivanje implementacionih detalja od korisnika objekta.
  * Delovi podataka u objektu su *polja instance*.
  * Procedure koje operisu nad tim podacima su *metode*.
  * Skup tih vrednosti je trenutno *stanje* objekta.
    * Kada se pozove metod na objekta, njegovo stanje se moze promeniti.
* Kljuc enkapsulacije je ne koristiti direktno polja instance.
  * Program bi trebalo da interaktuje sa njima samo preko njegovih metoda.
* Klase se mogu praviti *prosirivanje* drugih klasa.
  * U Javi postoji ``kosmicka superklasa'' naznava `Object`. Svi drugi objekti
    prosiruju ovo klasu.
* Koncept prosirivanje klase za dobijanje nove klase se naziva *nasledjivanje*.

### Objekti

* Tri kljucne karakteristike objekta:
  * *Ponasanje* objekta --- sta je moguce uraditi sa ovim objekto, ili koje
    metode je moguce primeniti na njega?
  * *Stanje* objekta --- kako se objekat menja kada se na njega pozovu
    te metode?
  * *Identitet* objekta --- kako se objekat razlikuje od drugog koji moze da
    ima isto ponasanje i stanje?
* Svi objekti koji su instance iste klase dele familiju koja podrzava ista
  *ponasanja*. Ta ponasanja se definisu metodama koje mogu pozvati.
* Svaki objekat sadrzi informacije kako on trenutno izgleda. To je njegovo
  *stanje*. Stanje objekta se moze promeniti tokom vremena pozivom njegovih
  metoda. 
  * Ako se njegovo stanje menja na drugi nacin nemamo enkapsulaciju.
* Svaki objekat je okarakterisan jedinstvenim *identitetom*.
  * Objekti koji su instanca iste klase *uvek* se razlikuju po identitetu, i
    *obicno* se razlikuju po stanju.

### Identifikovanje Klasa

* U objektn-orijentisanom programiranju nema pocetka, tj. ne pocinje se
  od `main` te se dalje kod pise linearno, vec se identifikuju klase i onda
  se njima dodaju metodi.
* Identifikovanje klasa je trazenje imenica u analizi problema, dok metodi
  odgovaraju odgovarajucim glagolima koji mogu da se koriste na tu imenicu.

### Relacija izmedju Klasa

1. *Zavisnost* (koristi)
  * Uvek hocemo da minimizujemo broj klasa koje zavise na druge klase.
    * Ako klasa A nije svesna od postojanju klase B, nije je briga za bilo
      kakve promene u B. (minimizacija *uparivanje*)
2. *Agregacija* (sadrzi)
3. *Nasledjivanje* (jeste)
  * Ako klasa A prosiruje klasu B, klasa A nasledjuje metode klase B, ali
    ima vise mogucnosti.
* UML (*Unified Modeling Language*) notacija za crtanje *dijagrama klasa* koje
  opisuju relacije izmedju njih.

## Koriscenje Predefinisanih Klasa

### Objekti i Objektne Promenljive

* Objekte prvo konstruisemo tako sto odredimo njihovo inicijalno stanje, onda
  mozemo primenjivati metode na njima.
* U Javi, koristimo *konstruktore* za konstruisanje novih instanci.
  * Konstruktor je specijalan metod ciji je cilj da konstruise i inicijalizuje
    objekat.
  * Konstruktor uvek ima isto ime kao ime klase.
  * Za konstruisanje novog objekta spajamo operator `new` sa konstruktorom:
```java
    new Date()
```
* Taj objekat mozemo onda koristiti kao argument nekog drugog metoda:
```java
    System.out.println(new Data());
```
* Mozemo takonje primenjivati metode na njega:
```java
    String s = new Data().toString();
```
* Obicno, hocemo da cuvamo referencu objekat u *objektnoj promenljivoj* 
  kako bi ga koristili vise puta:
```java
    Data birthday = new Data();
```
```
                             ___________
              ______        |    Date   |
    birthday=|______|-----> |^^^^^^^^^^^|
                            |           |
                            |___________|
```
* Postoji razlika izmedju objekta i objektne promenljive:
```java
    Data deadline; // ne referise ni na jedan objekat
    deadline.toString(); // nije moguce
    deadline = new Data(); // sada referise na jednu instancu klase Data
    deadline = null; // deadline je inicijalizovan i eksplicitno ne pokazuje
                     // ni na jedan objekat
```

### LocalDate Klasa Javine Biblioteke

* Za inicijalizaciju objekta klase `LocalDate` nije potrebno koristiti
  konstruktor, vec staticku *fabricku metodu* koja zatim poziva konstruktor.
```java
    // konstruise novi objekat sa trenutnim datumom.
    LocalDate date= LocalDate.now(); 

    // konstruise novi objekat sa zadatim datuom.
    LocalDate date = LocalDate.of(1999, 12, 31); 
    LocalDate aThousandDaysLater = date.plusDays(1000);
    int year = date.getYear(); // 1999
    int month = date.getMonthValue(); // 12
    int day = date.getDatOfMonth(); // 31
```

### Mutator i Accessor Metodi

```java
    LocalDate aThousandDaysLater = date.plusDays(1000);
```
* Sta se desava sa `date` nakon poziva metode `plusDays()`?
* Da li se promenio da bude 1000 godina kasnije?
  * Ispostavlja se da je idalje isti, jer metod `plusDays()` daje novi
    objekat koji se dodeljuje `aThousandDaysLater` promenljivi.
* Kazemo da `plusDays` metod *ne mutira* objekat nad kojim se poziva.
* Svi drugi metodi koji nemaju stanje objekta su *mutirajuci metodi*.
* Metodi koji samo pristupaju objektima bez da ih menjaju nazivaju se
  *pristupajuci metodi*.

## Definisanje klasa

```java
    class ImeKlase {
        polje1 
        polje2
        ...
        konstructor1
        konstructor2
        ...
        metod1
        metod2
        ...
    }
```

* Razmotrimo sledecu jednostavnu klasu `Zaposleni`:
```java
    class Zaposleni {
        // instance polja
        private String ime;
        private double plata;
        private LocalDate datumZaposljavanja;

        // construktor
        public Zaposleni(String i, double p, int godina, int mesec, int dan) {
            ime = i;
            plata = p;
            datumZaposljavanja = LocalDate.of(godina, mesec, dan);
        }

        // metode
        public String getIme() {
            return ime;
        }
        
        public double getPlata() {
            return plata;
        }

        public LocalDate getDatumZaposljavanja() {
            return datumZaposljavanja;
        }

        public void povecajPlatu(double procenat) {
            double povecanje = plata * procenat / 100;
            plata += povecanje;
        }
    }
```
* Hocemo da popunimo niz zaposlenih sa tri objekta `Zaposleni`:
```java
    Zaposleni[] zaposleni = new Zaposleni[3];

    zaposleni[0] = new Zaposleni("Pera Peric", 1000, 2000, 4, 3);
    zaposleni[1] = new Zaposleni("Mara Maric", 1200, 2000, 5, 2);
    zaposleni[2] = new Zaposleni("Kata Katic", 1100, 2000, 4, 1);
```
* Zatim hocemo da povecamo svima platu za 5%, i da ih sve ispisemo:
```java
    for (Zaposleni z : zaposleni) {
        z.povecajPlatu(5);
    }
    for (Zaposleni z : zaposleni) {
        System.out.printf("ime=" + z.getIme()
            + ", plata=" + z.getPlata()
            + ", datumZaposljenja=" + z.getDatumZaposljavanja());
    }
```

### Raspravljamo o Klasi Zaposleni

* Kao sto vidimo kalsa `Zaposleni` ime jedan kostruktor i cetiri metode:
```java
    public Zaposleni(String i, double p, int godina, int mesec, int dan) 
    public String getIme() 
    public double getPlata() 
    public LocalDate getDatumZaposljavanja() 
    public void povecajPlatu(double procenat) 
```
* Svi oni imaju kljucno red `public` sto znaci da bilo koji druga klasa
  moze da pozove te metode.
* Sada primetimo instance polja koje sadrze podatke:
```java
        private String ime;
        private double plata;
        private LocalDate datumZaposljavanja;
```
* Kljucna rec `private` znaci da im se jedino moze pristupiti preko metoda
  klase `Zaposleni`. Ni jedan drugi metod van klase ne moze pristupiti ovim
  poljima.
* Primetimo jos da instance polja sadrze mogu da sadrze objekte. 
  * U nasem slucaju su to `String` i `LocalDate`.

### Prvi Korakci sa Konstruktorom

* Primetimo kada se napravi instanca klase `Zaposleni`, kodom:
```java
    new Zaposleni("Pera Peric", 1000, 2000, 1, 1);
```
* tada postavljamo instance polja kao:
```java
    ime = "Pera Peric";
    plata = 1000;
    datumZaposljavanja = LocalDate.of(1950, 1, 1);
```
* Postoji jasna razlika izmedju konstruktora i drugih metoda.
  * Konstruktor ima isto ime kao klasa.
  * Klasa moze da ima vise od jednog konstruktora.
  * Konstruktor moze da ime nula, jedan, ili vise parametara.
  * Konstruktor nema return vrednost
  * Konstruktor se uvek poziva sa `new` operatorom.

### Implicitni i Eksplicitni parametri

* Posmatrajmo sledeci metod, pozvan sa `z1.povecajPlatu(5)`:
```java
    public void povecajPlatu(double procenat) {
        double povecanje = plata * procenat / 100;
        plata += povecanje;
    }
    // poziv izvrsava sledece
    double povecanje = z1.plata * 5 / 100;
    z1.plata += povecanje;
```
* Ova metoda ima dva parametra:
  1. *Implicitni* parametar je objekat tipa `Zaposleni` koji se pojavljuje
     pre imena metode.
     * Ne deklarisu se u deklaraciji metode vec se prodrazumeva.
     * Kljucna rec `this` referisi na taj parametar.
  2. *Eksplicitni* parametar je broj koji se pojavljuje u zagradama metode.
    * Deklarise se u zagradama i moze da ih ima vise.

### Benefit Enkapsulacije

* Posmatrajmo sledece jednostavne metode `getIme, 
  getPlata, getDatumZaposljavanja`.
* Ovi su pristupajuci metodi, i kako jednostavno vracaju vrednosti instance
  polja, nazivaju se *pristupnici poljima*.
* Zar ne bi bilo lakse napraviti samo polja javnim, umesto da imamo posebne
  pristupajuce metode?
  * Polje `ime` je read-only polje. Kada se postavi u konstruktoru ostaje 
    nepromenjeno, jer ne postoji ni jedan metod koji ga menja. Time 
    garantujemo da to polje nece postati koruptirano.
  * Slicno polje `plata` nije read-only, ali jedino se menja u metodi
    `povecajPlatu`. Sto u praksi znaci ako imamo pogresnu vrednost, 
    dovoljno je debagovati tu metodu, a ne traziti po citavom kodu
    gde smo promenili ovu vrednost.
* Nekada hocemo da uzimamo i postavljamo vrednosti instance polja:
  * Privatno polje podataka;
  * Javan pristupajuci metod; i
  * Javni mutator metod.
* Sto se cini naporno, ali ima benefite:
  1. Moce se promeniti interna implementacija bez uticaja na bilo koji drugi
     kod sem metoda te klase.
  2. Mutator metodi mogu izvrsavati proveru gresaka, kako kod koji postavlja
     vrednost nema potrebu da se zamara sa tim postupkom.

### Klasni pristup Pristupi

* Vec znamo da metod moze da ima pristup privatnim podacima objekta nad kojim
  se on poziva. Ali ono sto je iznenadjujuce, je to da metod moze pristupiti
  privatnim podacima *svih objekata te klase*.
* Razmotrimo sledecu funkciju:
```java
class Zaposleni {
    ...
    public boolean equals(Zaposleni other) {
        return this.name.equals(other.name);
    }
    ...
}
```

### Privatni Metode

* Nekada zelimo da podelimo neki metod na manje delova, ili jos bolje ako se
  neki blok javlja u vise metoda neke klase zelimo da taj blok apstrakujemo.
  * On mozda nije kompletan da bi se pozivao van klase, zato ga mozemo 
    naciniti privatnim, i odvojiti ga od ostalih javnih metoda.
* Privatni metod se jednostavno implementira koriscenjem kljucne reci 
  `private`.

### Final Instance Polja

* Moguce je definisati instancu polja kao `final`.
  * Ova polja se *moraju* inicijalizovati kada se objekat konstruise, tj.
    moramo garantovati da ce polje biti postavljeno pre kraja konstruktora.
* Nakon toga nikada nije moguce modifikovati to polje.
* `final` se koristi za polja ciji je tip primitivan ili imutabilna klasa.

## Staticna Polja i Metode

### Staticna Polja

* Ako se polje definise kao `static`, onda postoji samo jedna promenljiva
  po klasi.

### Staticne Konstante

* Definisu se sa `static final` i moze im se pristupiti bez stvaranja 
  instance te klase, na primer `Math.PI`.

### Staticne Metode

* Staticne metode ne operisu na objektu, drugim recima nemaju impliciti
  parametar.
  * Staticne metode ne mogu da pristupe instancim poljima objekte, ali mogu
    staticnim poljima te klase.
* Staticne metode koristimo u dve situacije:
  1. Kada metod nema potrebu da pristupa stanju objekta zato sto su svi
     potrebni parametri eksplicitni parametri.
  2. Kada metodi samo treba pristup statickio poljima klase.

### Fabricke Metode

### Main Metod

* Staticne metode se mogu pozivati bez instance klase u kojoj se nalaze, pa 
  je zato `main` metod static jer se nikada ne konstruise objekat 
  klase `Main`.

## Parametri Metoda

* *poziv po vrednosti* --- metod dobija samo vrednosti koje pozivalac pruza.
* *poziv po referenci* --- metod dobija *lokacuju* promenljive koju pruza 
  pozivalac. 
  * metoda moze da *menja* vrednosti promenljive
* Java *uvek* koristi poziv po vrednosti.
* Ali medjutim postoje dve vrste parametara:
  1. Primitivnog tipa (brojevi, `boolean`)
    * kopira *vrednost* u parametar metode
  2. Objektne reference
    * kopira *referencu* u parametar metode
* Mnogi misle da je poziv po referenci ondnosu na poziv po vrednosti
  objektne reference, te prave greske kao sto je `swap(obj1, obj2)` sto
  nije moguce jer se referenca na obj1 i obj2 kopira, tj. reference
  *objekta su prosledjeni po vrednosti*.
* Ukratko:
  1. Metoda ne moze da modifikuje parametre primitivih tipova.
  2. Metoda moze da promeni stanje objekta.
  3. Metoda ne moze da primeni da neka promenljiva referise na
     neki drugi objekat.

## Konstrukcije Objekta

### Overloading

* Mogucnost da neka klasa ima vise konstruktora, generalno vise funkcija
  istog naziva se *overloading*.
* Kompajler bira metod koji poziva u zavisnosti od parametara.
  * compile-timer error se desi kada kompajler ne moze da.
* Proces nalazenja odgovarajuceg metoda naziva se *overloading resolution*.

### Default-no inicijalizovanje polja

* Ako se u konstruktoru ne inicijalizuje vrednost nekog polja, ona se 
  automacki inicijalizuje default-nom vrednoscu tog polja (`0, false, null`, 
  za broj, `boolean`, i objekat respektivno)
  * Zbog citljivosti ovo se izbegava.

### Konstruktor bez argumenata

* Mnoge kalse imaju konstruktore bez argumenata, koje postavljaju 
  inicijalne vrednosti polja.
  * Ako ne navedemo ovaj konstruktor, java nam pruza jedan 
    konstruktor bez argumenata koji svako polje postavi na default vrednost,
    ali opet to je losa praksa zbog citljivosti.
* Ako klasa ima samo konstruktor sa argumentima, nije dozvoljeno da se
  poziva default-ni konstruktor koji pruza java.

### Eksplicitno inicijalizovanje polja

* Moguce je jednostavno pridruziti vrednost bilo kom polju u definiciji klase.
```java
    class Zaposleni {
        private String ime = "";
        ...
    }
```

### Ime parametara

* Nekada je frustrirajuce smisljati nova imena parametara kako bi se 
  razlikovala od imena polja. 
* Neki programeri vole da dodaju prefiks `a` svakom parametru.
* Dok drugi vole da koriste ista imena kao i imena polja, ali pri koriscenju
  polja koriste kljucnu rec ``this``.
* Primer oba nacina:
```java
    // Ovo nema smisla na srpskom
    Zaposleni(String aName, double aPlata) {
        name = aName;
        plata = aPlata;
    }
    // Drugi metod je bolji
    Zaposleni(String name, double plata) {
        this.name = name;
        this.plata = plata;
    }
```

### Pozivanje drugog konstruktora

* Kljucna rec `this` ima jos jedno znacenje:
* Ako je *prva naredba konstruktora* oblika `this(...)`, onda konstruktora
  poziva drugi konstruktor iste klase.
```java
   Zaposleni(double plata) {
       this("Zaposleni #" + nextId, plata);
       nextId++;
   }
```

### Inicijalizacioni blokovi

* Vec smo videli 2 nacina za inicijalizovanje polja podataka:
  1. inicijalizacija u konstruktoru
  2. inicijalizacija u deklaraciji 
* Postoji i treci nacin koji se zove *inicijalizacioni blok*.
* Klasa moze da ima blokove koda. Ovi blokovi se izvrsavaju kada god se
  objekat te klase napravi.
```java
    class Zaposleni {

        private static int nextId;
        private int id;
        ...

        // inicijalizacioni blok
        {
            id = nextId;
            nextId++;
        }

        ...
    }
```
* Detaljan proces izbrsavanja konstruktora:
  1. Sva polja su inicijalizovana na default-ne vrednosti (`0, false, null`)
  2. Svi inicijalizatori polja i inicijalizacioni bolokovi su izvrseni, u
     redu u kome su nalaze u kodu.
  3. Ako prva linija konstruktor pozove drugi konstruktor, onda se  
     izvrsava telo drugog konstruktora.
  4. Izvrsava se telo konstruktora
* Sledeci kod prikazuje:
  1. Overloading
  2. Poziv drugog konstruktora sa this
  3. Konstruktor bez argumenata
  4. inicijalizacioni blok
  5. inicijalizacija polja
```java
class Zaposleni {

    private static int nextId;

    private int id;
    private String name = ""; // inicijalizacija polja
    private double plata;

    // Staticni inicijalizacioni blok
    static
    {
        Random rand = new Random();
        nextId = rand.nextInt(1000);
    }

    // inicijalizacioni blok
    {
        id = nextId;
        nextId++;
    }
    
    public Zaposleni(String name, double plata) {
        this.name = name;
        this.plata = plata;
    }

    public Zaposleni(double plata) {
        // Poziv drugog konstruktora sa this
        this("Zaposleni #" + nextId, plata); 
    }

    public Zaposleni() {
        // Prazan konstruktor
    }

    public int getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public double getPlata() {
        return plata;
    }
}
```

### Unistavanje Objekata i `finalize` Metod

* U javi ne postoji koncept unistenja objekta, kada nam vise nije potreban.
* Time se bavi kolektor smeca.
* Ipak neki objekti koriste neke resurse koji nisu memorija, u tim 
  slucajevima nam je bitno da resursi budu oslobodjeni kada nam vise
  nisu potrebni.
* Za metodu koja se bavi oslobadjanje koristimo kljucnu rec `finalize`.

## Paketi

* Moguce je grupisati klase u kolekcije nazvane *paketi*.
* Paketi funkcionisu kao direktorijumi, te pruzaju bolje grupisanje.
* Paketi sluze kako ne bi doslo do konflikta sa imenima klasa. 
  * Na primer dva programera mogu klasu da nazovu istim imenom, ali ako 
    se oni nalaze u razlicitim paketima nemamo konflikt uvek znamo 
    koju klasu koristimo.

### Uvozenje klasa

* Klasa moze da koristi druge klase iz svog paketa, ali moze da koristi
  i javne klase drugih paketa.
* Pristupanje javnih klase drugih paketa moguce je na dva nacina:
  1. Jednostavno dodamo puno ime paketa ispred imena klase.
```java
    java.time.LocalDate danas = new java.time.LocalDate.now();
```
  2. Uvezemo klasu pomocu kljucne reci `import`.
```java
    import java.time.LocalDate;
    ... 
    LocalDate danas = new LocalData.now();
```
* Moguce je koristiti i `*` da importujemo sve klase iz nekog paketa:
  `import java.util.*`
* Ako klase imaju isto ime u dva razlicita uvezena paketa, mora se
  eksplicitno uvesti i klase iz paketa koju koristimo, a ako nam trebaju
  obe klase onda moramo da koristimo metodu 1.

### Staticno uvezenje

* Klasicno uvezenje zabranjuje koriscenje statickih polja i metoda, zbog
  toga se koristi kljucna rec `static` pri uvozenju. Pa nesto kao sto je:
```java
    import static java.util.Math.*;
    sqrt(pow(x) + pow(y)) // ekvivalentno je sa
    Math.sqrt(Math.pow(x) + Math.pow(y))
```
  
### Dodavanje Klasa u Paket

* Da bi dodali klasu u paket moramo da definisemo u kom paketu se ta
  klasa nalazi pre same definicije klase, to radimo na sledeci nacin:
```java
package org.nesto1.nesto2;

class Klasa {
    ...
}
```
* Ako se to ne definise klasa pripada *default-nom paketu*.
  * On nema ime 

### Doseg paketa

* `public` moze da se koristi u bilo kojoj klasi.
* `private` moze da se koristi samo u klasi u kojoj se definise.
* ako se ne specifikuje moguc je pristup iz svih klasa jednog paketa.

## Putanja Klase

* Fajlovi klasa se skladiste u poddirektorijume, tako da je putanja do 
  fajla klase ista kao i putanja do pakata.
* Fajlovi klase se takodje skladiste u JAR (Java archive) fajlove. 
  * JAR fajl sadrzi kompresovane falove klasa i poddirektorijume.
* Za deljenje klasa izmedju programera potrebno je:
  1. Staviti fajlove klasa u direktorijum.
  2. Staviti JAR fajlove.
  3. Postaviti *class path*. 
    * Putanja klase je kolekcija svih lokacija koje sadrzi fajlove klasa.
      * U UNIXu, elementi putanje klasa su razdvojeni sa `::`:
* Razmotrimo jednostavan primer:
```
/home/user/classdir:.:/home/user/archives/archive.jar
```
* Pretpostavimo da virtualna masina trazi `org.Zaposleni.class`
* Trazi po redu u: 
  1. `/home/user/classdir/org/Zaposleni.class`
  2. `org/Zaposleni.class` od pocetka radnog direktorijuma
  3. `org/Zaposleni.class` u 
     `/home/user/archives/archive.jar`

### Postavljanje putanje klase

* Najbolje je postaviti putanju klase sa ``-classpath``:
```
java -classpath /home/user/classdir:.:/home/user/archives/archive.jar MyProg
```
* Druga mogucnost je preko `CLASSPATH` promenljive.
```
export CLASSPATH=/home/user/classdir:.:/home/user/archives/archive.jar
```
* U drugom slucaja putalja klase je postavljenja sve dok je shell radi.

## Dokumentacioni Komentari

* JDK sadrzi korisnu alatku za generisanje HTML dokumentacije iz source
  koda nazvanu `javadoc`.
* Dodavanje `/**` na pocetak komentara moguce je stvoriti profesionalnu
  dokumentaciju.

### Umetanje komentara

* `javadoc` izvlaci informacije iz sledeci fajlova:
  * paketi
  * javne kalse i interfejsi
  * javna i zasticena polja
  * javne i zasticene konstruktore i metode
* Svaki komentar se nalazi *iznad* informacije koju opisuje i pocinje
  sa `/**` a zavrsava se sa `*/`
* Svaki komentar sadrzi *slobodan tekst*, zajedno sa *tagovima*.
  * Tagovi pocinju sa `@`.
* *Prva recenica* bi trebala da bude *kratak opis*. 
* Slobodan tekst moze da sadrzi HTML elemente.

### Komentari klasa

* Komentari klasa se nalaze *ispod* `import` naredbi, i *direktno iznad*
  definicije *klase*.
```java
/**
* {@code Karta} objekat predstavlja kartu za igranje, kao sto je 
* "Kraljica Srce". Karta ima znak (Karo, Herc,
* Pik, ili Tref) i vrednost (1 = Kec, 2 . . . 10, 11 = Zandar,
* 12 = Kraljica, 13 = Kralj)
*/
public class Karta 
{
   ...
}
```

### Komentar metoda

* Svaki komentar metoda mora da se nalazi *direktno iznad* metode. 
* Pored generalnih tagova moze da sadrzi:
  * `@param` *promenljiva opis*
  * `@return` *opis*
  * `@throws` *clasa opis*
```java
    /** 
     * Povecava platu Zaposlenom
     * @param procenat procenat povecanja plate
     * @return sumu povecanja plate
     */
    public double povecajPlatu(double procenat) {
        double povecanje = this.plata * procenat / 100;
        this.plata += povecanje;
        return povecanje;
    }
```

### Komentar polja

* Potrebno je samo dokumentovati javna polja, generalno staticne konstante.
```java
    /**
    * "Herc" znak karte
    */
    public static final int HERC = 1;
```

### Komentari generalno 

* Tagovi koji se mogu koristiti:
  * `@author` *ime*
  * `@version` *text*
  * `@deprecated` *text*
  * `@see` *referenca*
  * `{@link paket.klasa#[polje/konstruktor/metoda] labela}`

### Komentari Paketa i Pregleda 

* Za komentarisanje pakete potrebno je dodati novi fajl za svaki paket.
  1. `package.html` ili;
  2. `package-info.java`
* Moguce je imati i *overview* komentar koji se nalazi u roditeljskom
  durektorijumu projekta pod nazivom `overview.html`.

### Izvlacenje dokumentacije iz komentara

1. Udji u direktorijum sa source fajlovima koji se dokumentisu.
  * Ako postoji `overview.html` on se mora nalaziti u tom direktorijumu.
2. Pozovi komandu: 
```
javadoc -d docDirektorijum imePaketa1 imePaketa2 ...
```

## Hintovi za Dizajniranje Klasa

1. *Uvek cuvaj podatke privatnim.*
2. *Uvek inicijalizuj podatke.*
3. *Nemoj da koristis previse osnovnih tipova u klasi.*
  * Na primer ako `Potrosac` ima polja `ulica, grad, drzava, zip` zameni
    sa novim objektom `Adresa`.
4. *Ne treba svim poljima zasebi pristupajuci i mutirajuci metod.*
5. *Razdvoji klase koje imaju previse odgovornosti*.
6. *Neka imena kalsa i metodi oznacavaju njigove odgovornosti.*
  * Dobra praksa je koristiti imenicu, ili imenicu sa pridevom za clasu, a
    sto se metoda tice one su glagoli i obicno za pristupajuce se koristi
    prefix `get`, a za mutirajuci se korsiti prefix `set`.
7. *Preferisi imutabilne klase*.
  * Zbog visenitnosti.

# Nasledjivanje

* Ideja *nasledjivanja* je stvaranje novih klasa na osnovu vec postojecih.
* Nasledjivanjem se naslede sve metode i polja iz vec postojecih klasa, a
  pri tome moguce je dodavanje novih polja i metoda, ili modifikacija vec
  postojecih.
* *Refleksija* je mogucnost nalazenja informacija o klasama u pokrenutom
  programu.

## Klase, Superklase, Podklase

* Posmatramo klasu `Zaposlen`. I neka u nasoj kompaniji Menadjeri razlikuju
  od ostalih Zaposlenih. U ovom slucaju nam je potrebno `nasledjivanje`, jer
  postoji ocigledna relacija `je` izmedju `Menadjer` i `Zaposleni`.
  * Svaki menadjer *je* zaposleni.

### Definisanje podklasa

* `Menadjer` nasledjuje `Zaposleni` definisempo pomocu kljucne reci `extends`,
  na sledeci nacin:
```java
    public class Menadjer extends Zaposleni {
        ...
    }
```
* `extends` ukazuje na to da pravimo novu klasu koja je izvedena iz
  postojace klase.
  * Postojaca klase se naziva *superklasa, bazna klasa, roditeljska klasa*.
  * Nova klasa se naziva *podklasa, izvedena klasa, naslednicka klasa*.
* `Zaposleni` je superklasa, ali ne zbog svoje superiornosti nad svojim
  podklasama, *suprotno je tacno*:
  * Podklase imaju *vise* funkcionalnosti od njigovih superklasa.
```java
    public class Menadjer extends Zaposleni {
        private double bonus;
        ...
        public void setBonus(double bonus) {
            this.bonus = bonus;
        }
    }
```
* Nad objektom klase `Menadjer` moguce je pozvati metodu `setBonus`.
* Naravno moguce je koristiti `setName`... nad objektom klase `Menadjer`.
* Slicno su preuzata i sva polja iz klase `Zaposlen`.
* Kada se definise podklasa prosirivanje njene superklase, dovoljno je
  definisati *razlike* izmedju njih.

### Overriding Metode

* Neko od metoda klase `Menadjer` se ne slazu sa metodama iz `Zaposlen`.
* Na primer `getPlata` bi trebala da uracuna i `bonus`.
* Potrebno je pruziti novi metod da bi *redefinisali* (engl. *override*) 
  metod superklase.
```java
    public double getPlata() {
        return plata + bonus; // ne radi
    }
```
* Samo `Zaposleni` ima direktan pristup promenljivi `plata`.
```java
    public double getPlata() {
        double osnovnaPlata = getPlata(); // ne radi
        return osnovnaPlata + bonus;
    }
```
* Ovde dobijamo rekurziju.
* Moramo nekako ukazati da zelimo da pozovemo metod iz `getPlata()`, ali iz
  klase `Zaposleni`. 
  * To nam omogucava kljucna rec `super`.
```java
    public double getPlata() { 
        double osnovnaPlata = super.getPlata(); // radi
        return osnovnaPlata + bonus;
    }
```
* Zakljucak:
  * Mozemo *dodati* nova polja.
  * Mozemo *dodati* nove metode.
  * Mozemo *redefinisati* (engl. *override*) metode superklase.
  * Nije moguce brisanje polja ili metoda.

### Konstruktori podklase

* Da bi zavrsili primer moramo dodati konstruktor:
```java
    public Menadjer(String name, double plata) {
        super(name, plata);
        this.bonus = 0;
    }
```
* Ovde kljucna rec `super` ima drugacije znacenje.
  * `Menadjer` mora da inicijalizuje polja klase `Zaposleni` preko
    konstruktora.
  * Konstruktor superklase se poziva sa `super` gde parametri
    predstavljaju argumente konstruktora.
* Ako se konstruktor superklase ne pozove eksplicitno onda se poziva
  konstruktor bez argumenata.
  * Dolazi do greske ako superklase nema konstruktor bez argumenata.
* Posmatramo sledeci kod:
```java
Menadjer gazda = new Menadjer("Pera Peric", 100000, 4000);

Zaposleni[] radnici = new Zaposleni[3];

radnici[0] = gazda;
radnici[1] = new Zaposleni("Mara Maric", 50000);
radnici[2] = new Zaposleni("Niki Nikic", 40000);

for (Zaposleni radnik : radnici) {
    System.out.println(radnik.getName() + " " + radnik.getPlata());
}
```
* Ovde imamo tri objekta radnika, od kojih su dva iz klase `Zaposleni`, a
  jedan iz klase `Menadjer`.
* Kada pozovemo `radnik.getPlata()` deklarisani tip objekta radnik je
  `Zaposleni` ali objekat `radnik` moze da referise ili na `Zaposleni` ili
  na `Menadjer`.
  * Posledica toga je da u zavisnosti od *pravog* tipa promenljive `randik`,
    izvrsava se druga 
* Cinjenica da jedna objektna promenljiva moze da referise na vise tipova
  se naziva *polimorfizam* (engl. *polymorphism*). 
* Biranje odgovarajuce metode u izvrsavanju se naziva *dinamicko povezivanje*
  (eng. *dynamic binding*).

### Hijerarhija Nasledjivanja

* Kolekcija svih klasa koje nasledjuju zajednicku superklasu se naziva
  *hijerarhija nasledjivanja*. 
* Put od neke klase do svih predaka u hijerarhiji nasledjivanja naziva se
  *lanac nasledjivanja*.
```
                Zaposleni
                    ^
                    |
        -------------------------
        |           |           |
    Menadjer    Sekretar    Programer
       |
    Direktor
```

### Polimorfizam

* Prirodan nacin odredjivanje da li je nasledjivanje dobar dizaj podataka,
  je pravilo *je*.
  * Na primer, Svaki menadjer *je* zaposleni, prirodno obrnuto nije tacno.
* Drugi nacin formulisanja ovog pravila je *princim substitucije* 
  (engl. *substitution principle*), on kaze da mozes koristiti 
  podklasni objekat ukoliko program ocekuje superklasni objekat.
  * Na prime, mozes dodeliti podklasni objekat u superklasnoj promenljivoj.
```java
  Zaposleni radnik;
  radnik = new Zaposleni(...);
  radnik = new Menadjer(...);
```
* Objekte promenljive su *polimofne* (engl. *polymorphic*).
  * Svaka objektna promenljiva neke klase moze da referise na objekat 
    te klase, ili bilo koji objekat njene podklase.
  * Ali nije moguce dodeliti superklasi referencu neke klase.
    * Razlog: Nisu svi zaposleni menadjeri.

### Razumevanje Poziva Metoda

* Neka je pozvana `x.f(args)`, gde je `x` implicitni parametar, deklarisan
  tako da je objekat klase `C`.
  1. Kompajler trazi deklarisani tip objekta i ime metode. Mozemo da imamo
     vise metoda sa imenom `f`. Kompajler numerise sve metode sa imenom `f` u
     klasi `C` i sve dostupne metode nazvane `f` u superklasama od `C`.
     * Posledica: Imamo sve moguce metode za kandidate.
  2. Kompajler pronalazi tipove argumenata u pozivu. Ako je medju svim 
     kandidatima postoji jedinstveni metod sa zadatim parametrima on se
     poziva (*overloading resolution*).
     * Posledica: Suzili smo skup kandidata na sve koji imaju iste parametre.
  3. Ako je metod `private, static, final` ili konstruktur, tada
     kompajler zna tacno koji metod da pozove (*static binding*).
     U suprotonm metod za pozivanje zavisi od stvarnog tipa implicitnog 
     parametra.
     * Posledica: Koristimo dinamicko povezivanje (*dynamic binding*) u
       izvrsavanju.
  4. Program je pokrenut i koristi dinamicko povezivanje da pozove metod, 
     tada moramo naci *pravi* tip objekta na koji `x` referise.
     Pretpostavimo da je to tip `D` podklasa od `C`. Ako `D` definise metod
     `f(args)` metod se pozove, u suprotonom se trazise metod u superklasi
     od `D`, itd.
     * Virtualna masina odrzava *tabelu metoda*, kada se pozove neki metod
       on se cuva tabeli, kako se ne bi trazio ponovo.
* Dinamicko povezivanje ima osobinu da ucini program *nadogradivim* bez
  potrebe za modifikovanje postojaceg koda.

### Zaustavljanje Nasledjivanja: Finalne Klase i Metode

* Klase koje se ne mogu prosiriti se nazivaju *finalne* klase, i koriste
  kljucno rec `final`.
```java
    public final class Direktor extends Menadjer {
        ...
    }
```
* Moguce je i da metodi budu finalni, tj. nijedna podklase ne moze da
  redefinise (*override*) taj metod.
```java
    public final String getName() {
        return this.name;
    }
```
* Postoji samo jedan dobar razlog deklarisati klasu kao `final`.
  * Da bi obezbedili da se njena semantika nece promeniti u podklasi.
* Neki programeri smatraju da se svi metodi trebaju deklarisati kao
  `final` sem ako zelimo polimorfizam.
  * C++ radi to.
* Ako metod nije redefinisan/overriden, i kratak je, kompajler moze 
  optimizovati poziv metoda, procesom nazvanim *inlining*. (samo ako je 
  `final`, jer inace ne zna sa kojim kodom da zameni)

### Kastovanje

* Kao sto je potrebna konverzija iz float u int, isto je potrebna 
  konverzija objektne reference jedne klase u drugu.
```java
    Menadjer sef = (Menadjer) radnici[0];
    Menadjer sef = (Menadjer) radnici[1]; // Greska!
```
* Zbog toga ako se ne uhvati `ClassCastException` program staje sa 
  izvrsavanje.
```java
    if (radnici[1] instanceof Menadjer) {
        sef = (Menadjer) radnici[1];
    }
```
* Moguce je kastovati samo postujuci hijerarhiju nasledjivanja.
* Koristimo `instanceof` da proverima da li je objekat podklasa 
  neke superklase
* Jedini razlog zasto zelimo kastovanje objekta je ukoliko klasa u koju
  kastujemo sadrzi neki metod koji ne postoji u superklasi.

### Apstraktne Klase

* Kako idemo uz hijerarhiju nasledjivanja klase postaju sve vise generalne
  i verovatno vise apstrakten. 
* Nekada je ta klasa toliko apstraktna de se nikada nece napraviti 
  instanca te klase.
* Primer `Osoba` moze da bude superklasa za `Zaposlenog`
```java
    public abstract class Osoba {
        private String name;
        public abstract String getOpis();
    }
```
* Abstraktne metode sluze za opisivanje metoda koje trebaju implementirati
  podklase.
* Kada se nasledjuje abstraktna klase:
  1. Moguce je ostaviti neke, ili sve abstraktne metode nedefinisane,
     ali tada ta klasa takodje mora da bude apstraktna.
  2. Ili da definisemo sve metode, tada podklasa nije vise apstraktna.

### Zasticeni pristup

* Kada zelimo da dozovolimo podklasi da pristupa poljima super
  klase, tada deklarisemo to polje kao `protected`.
* `protected` treba koristite oprezno!
  * Pretpostavimo da je klasa ima `protected` polja.
  * Neko moze da nasledi tu klasu i time dobije pristup tim poljima.
  * Ako zamenimo to polja u `private` remetimo sve te podklase
    koje koriste ta polja.
* Vise misla imaju `protected` metode.
* Ukratko o svim pristupajucim modifikatorima:
  1. Vidljiv samo svojoj klasi (`private`)
  2. Vidljiv svetu (`public`)
  3. Vidljiv paketu i svim podklasama (`protected`)
  4. Vidljiv paketu (Modifikator nije potreban).

## Object: Kosmicna Superklasa

* Klasa `Object` je ultimativni naslednik, tj. svaka klasa u Javi
  nasledjuje `Object`.
* Moguce je koristiti promenljivu tipa `Object` za referisanje 
  objekta bilo kog tipa:
```java
    Object obj = new Zaposleni("Pera Peric", 3400);
```
* Ali ovo koristimo samo za cuvanje bilo kog tipa, ako hocemo da koristimo
  taj objekat moramo ga pre toga kastovati.
* U Javi, samo *primitivni tipovi* (brojevi, karakteri, i `boolean` vrednosti)
  nisu objekti!
* Svi nizovi nasledjuju `Object` klasau.

### Metod `equals`

* Metod `equals` u `Object` klasi ispituje da li se jedan objekat
  smatra jednakim sa drugim objektom.
  * Tacnije u `Object` klasi je implementirao tako sto proverava da li
    objektna promenljiva referisa na isti objekat kao neka druga objektna
    promenljiva.
* Ali u vecini slucajeva nas zanima da je je stanje nekog objekta
  isto kao i stanje nekog drugog objekta.
  * Zbog toga mi implementiramo metod `equal` za nasu klasu.
```java
    public boolean equals(Object drugiObjekat) {
        if (this == drugiObjekat) {
            return true;
        } 

        if (drugiObjekat == null) {
            return false;
        }

        if (getClass() != drugiObjekat.getClass()) {
            return false;
        }

        Zaposleni drugi = (Zaposleni) drugiObjekat;

        return name.equals(drugi.name) &&
               plata == drugi.plata;
    }
```
* Kada se definise `equals` metoda za podklasu, dobra praksa je 
  pozvati `equals` superklase.
```java
    public boolean equals(Object drugiObject) {
        if (!super.equals(drugiObject)) {
            return false;
        } 

        Menadzer drugi = (Menadzer) drugiObject;
        return bonus == drugi.bonus;
    }
```

### Testiranje jednakosti i nasledjivanja

* Kako se `equals` metod ponasa ako implicitni i eksplicitni parametar
  ne pripadaju istoj klasi?
* Ako je odgovor `false`:
  * Mnogi koriste `instanceof` ako hoce da provere da li je neki
    objekat neke klase:
```java
    if (!(drugiObjekat instanceof Zaposleni)) return false;
```
* Ovo znaci da se ostavlja mogucnost `drugiObjekat` moze da pripada
  nekoj podklasi. Ovo nije dobro! `equals` metod mora da ima sledece osobine:
  1. *Refleksivnost*: Za bilo koju ne-null referencu `x`, `x.equals(x)` vraca
     `true`.
  2. *Simetricnost*: Za bilo koju referencu `x` i `y`, `x.equals(y)` 
     vraca `true` akko `y.equals(x)` vraca `true`.
  3. *Tranzitivnost*: Za bilo koje reference `x`, `y`, i `z`, ako `x.equals(y)`
     vraca `true` i `y.equals(z)` vraca `true, onda i `x.equals(z)` mora
     da vraca `true`.
  4. *Koinzistentnost*: Ako se objekti na koje `x` i `y` referisu nisu
     promenili, tada novi poziv `x.equals(y)` vraca istu vrednost
     kao i pre.
  5. Za bilo koju ne-null referencu `x`, `x.equals(null)` vraca `false`.
* Nas primer sa `instanceof` krsi Simetricnost!
* Neki programeri smatraju da `getClass` test nije dobar, zato sto krsi
  princip substitucije. 
  * Primer: `AbstractSet` je superklasa za `TreeSet` i `HashSet`. 
    Ako hocemo da uporedimo dva skupa koja su implementira pomocu drveta
    ili pomocu hash tabele, metod sa getClass uvek vraca `false`.
* Zbog toga imamo 2 razlicita scenarija:
  1. Ako podklasa moze da ima svoj metod `equals`, zvog simetricnosti
     koristimo `getClass`.
  2. Ako je metod `equals` fiksan u superklase, tada koristimo `instanceof`
     test da bi omogucili razlicitim podklasama da bude jednake.
* Uputstvo za pisanje perfektnog `equals` metoda:
  1. Nazovemo eksplicitni parametar `drugiObjekat`.
  2. Proveravamo da li je `this` identican sa `drugObjekat`.
  3. Proveravamo da li je `drugiObjekat` `null`.
  4. Uporedjujemo klasu objekta `this` i `drugiObjekat`.
     Koristimo `getClass` ili `instanceof`, u zavisnosti od gore navedenog.
  5. Kastujemo `drugiObjekat` klasu obejkta `this`.
  6. Uporedjujemo polja.

### Metod `hashCode`

* Hash kod je celi broj izveden iz objekta.
* Ako su `x` i `y` dva razlicita objekta, tada njihovi hash codovi su 
  razliciti sa velikom verovatnocom. 
  (Moze da se desi da budu isti *rodjendanski paradox*)
  * Za stringove hash kod se racuna hornerovom metodom.
```java
    public int hashCode() {
        return Objects.hash(name, plata);
    }
```
* `equals` i `hashCode` moraju biti kompitablilni:
  * Ako `x.equals(y)` vraca `true`, tada mora da vazi 
    `x.hashCode() == y.hashCode()`, sa velikom verovatnocom naravno.

### Metod `toString`

* `toString` metod klase `Object` vraca string reprezentaciju tog objekta.
* Obicno `toStrgin` metod prati sledeci format: ime klase, pa polja 
  (ime, vrednost) u kockastim zagradama:
```java
    public String toString() {
        return super.toString() +
               "[bonus="  + this.bonus +
               "]";
    }
```
* `toString` je koristan iz 2 razloga:
  1. Kada nadovezemo na neki string sa operatorom `+` objekat `o` 
     automacki se pozova `o.toString()` koji se onda nadovezuje.
  2. Kada ispisujemo objekat `o` isto se automacki poziva `o.toString()`,
     te se ispisuje taj string.

## Dinamicki nizovi

* U javi obicno nizovi nisu dinamicki. Pa se zbog toga koristi `ArrayList` 
  klasa.
* `ArrayList` je *genericka klase* sa *tipiziranim parametrom*.
```java
    ArrayList<Zaposleni> radnici = new ArrayList<Zaposleni>();
    ArrayList<Zaposleni> radnici = new ArrayList<>(); // moze i ovako od SE 7
```
* Ovo se zove *dijamant* sintaksa zato sto zagrade `<>` lice na dijamant.
* Metod `add` sluzi da se doda novi element u `ArrayList`.
```java
    radnici.add(new Zaposleni("Pera Peric", 3000));
    radnici.add(new Zaposleni("Mara Peric", 3000));
```
* Kada se niz popuni do kraja, i hocemo da dodamo novi element,
  automacki se kreira veci niz i kopira sve elemente iz manjeg u veci niz.
* `size()` metod vraca broj popunjenih elemenata.
* `ensureCapacity(int velicina)` postavlja duzinu na `velicina`.
* `trimToSize()` smanjuje duzinu niza do zadnjeg popunjenog elementa.
  * Koristiti samo kada sigurno nece biti dodatnih elementa.

### Pristupanje Array List elementima

* Umesto `[]` sintakse za pristup ili promenu elementa u nizu, koriste
  se `get` i `set` metodi.
* Ako se prolazi kroz ceo niz umesto `get` i `set` lakse je 
  koristiti *for each*.
* Moguce je i brisanje elementa na nekoj poziciji sa `remove(int index)`
  metodom, ali nije efikasno za velike Array Liste, zato sto
  mora da kopira sve posle njega za jedno mesto.

## Objektni Zapakivaci (Wrappers) i Samozapakivanje (Autoboxing)

* Svi primitivni tipovi imaju odgovarajuce klase.
  * Primer: klasi `Integer` odgovara primitivni tip `int`.
* Ove klase se nazivaju *zapakivaci* (eng. *wrappers*).
* Imena: `Integer, Long, Short, Flaot, Double, Byte, Character, Boolean`.
  * Prvih sest nasledjuju zajednicku superklasu `Number`.
* Svi *zapakivaci* su imutabilni, tj. nije moguce promeniti vrednost
  nakon sto je vrednost zapakovana zapakivacem.
* Takodje su i `final`, pa ih nije moguce naslediti.
* Kako nije moguce formirati `ArrayList<int>` sa primitivnim tipom `int`,
  moguce je to uraditi sa zapakivacem `Integer`: `ArrayList<Integer>`.
* Na srecu lako je dodati novi element u `ArrayList<Integer> list`:
```java
    list.add(3); <-- samozapakivanje
    list.add(Integer.valueOf(3)); <-- rucno zapakivanje
```
* Ovo omogucuje konverzija koja se naziva *samozapakivanje* (engl. 
  *autoboxing*).
* Slicno vazi i za otpakivanje: `int n = list.get(i);`
* Operator `==`, testira samo da li objekti imaju identicnu memorijsku 
  lokaciju, pa sledece daje nedefinisano ponasanje:
```java
    Integer a = 1000;
    Integer b = 1000;
    if (a == b) ...
```
* Zbog toga koristimo metod `equals` za uporedjivanje upakovanih objekata.
* Zapakivanje i otpakivanje pruza *kompajler*, a ne virtualna masina.
* U Zapakivacima se nalaze neke osnovne metode, kao sto je konvertovanje
  stringa cifara u broj.
```java
    int x = Integer.parseInt(s);
```

## Metodi sa Promenljivim Brojem Parametara

* Ovi metodi se nekada zovu *varargs*.
  * Primer ovih metoda je `printf`. On je definisan kao:
```java
    public PrintStream printf(String format, Object... args);
```
  * `...` Oznacava da metod moze da primi bilo koliko objekata.
  * `printf`, zaprvaro, prima samo 2 parametara, od kojih je jedan `format`
    tipa `String`, a drugi `args` tipa `Object[]`.
* Kompajler svaki put transformise kod poziva metode sa promenljivim
  brojem parametra u parametra oblika `new Object[] {parm1, parm2,..., parmn}`
  pomocu samozapakivanja.
* Primer implementacije:
```java
    public static double max(double... values) {
        double maximum = Double.NEGATIVE_INFINITY;
        for (double val : values) {
            if (maximum < val) {
                maximum = val;
            }
        }
        return maximum;
    }

    double m = max(3.14, 40.4, -5); // kompajler ovo prevodi u:
    double m = max(new double[] { 3.14, 40.4, -5 });
```

## Enumeracione Klase

* Primer:
```java
    public enum Velicina { SMALL, MEDIUM, LARGE, EXTRA_LARGE };
```
* Ovako definisan tip je zapravo klasa, i ima tacno 4 instance, i nije moguce
  kreirati nove objekte.
* Za poredjenje je dovoljno koristiti `==`.
* Moguce je dodati konstruktore, metode, i polja u enumeracione klase:
```java
    public enum Size {
        SMALL("S"), MEDIUM("M"), LARGE("L"), EXTRA_LARGE("XL");

        private String abbreviation;

        private Size(SMALL abbreviation) {
            this.abbreviation = abbreviation;
        }

        public String getAbbraviation() {
            return abbreviation;
        }
    }
```
* Svi enumerisani tipovu su podklasa klase `Enum`.
  * Nasledjuju mnoge metode: `toString`, `valueOf`, `values`, `original`

## Refleksije


# Interfejs, Lambda Izrazi, i Unutrasnje Klase


