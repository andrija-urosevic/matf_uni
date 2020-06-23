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
* Apstraktne metode sluze za opisivanje metoda koje trebaju implementirati
  podklase.
* Kada se nasledjuje abstraktna klase:
  1. Moguce je ostaviti neke, ili sve apstraktne metode nedefinisane,
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

* *Biblioteka refleksije* pruza veoma velik broj alata za pisanje programa
  koji manipulisu Java kod dinamicno.
* Program koji analiza mogucnosti klasa nazivamo *reflektivan*.
* Koristi se za:
  * Analizu mogunosti klasa za vreme izvrsavanja
  * Ispitivanje objekata za vreme izvrsavanja
  * Implementiranje genericnog niza
  * Koristi `Method` objekat, koji radi kao funkcijskim pokazivaci
* Mocan je i kompleksan mehanizam, ali se samo koristi za pravljenje alata,
  ne za pravljenje aplikativnih programa.

## Hintovi za Dizajniranje Nasledjivanja 

1. *Stravi zajednicke operacije i polja u superklasu.*
2. *Ne koristi protected polja.*
3. *Koristi nasledjivanje za modeliranje 'je' relazije.*
4. *Ne koristi nasledjivanje sem ako svi nasledjeni metodi imaju smisla.*
5. *Ne menjaj ocekivano ponasanje pri redefinisanju metoda.*
6. *Koristi polimorfizam, ne informaciju tipa.*
7. *Ne koristi preterano refleksiju.*

# Interfejs, Lambda Izrazi, i Unutrasnje Klase

* *Intefejs* sluzi da bi se opisalo *sta* klase treba da rade, bez opisivanja
  *kako* to rade.
  * Klase *implementiraju* jedan ili vise interfejsa.
* *Lambda izrazi* su nacin za da opise blok coda koji moze da se izvrsi 
  kasnije.
* *Unitrasnje klase* definisu se unutar neke druge klase, i njihovi metodi
  mogu da pristupe poljima te druge klase.

## Interfejs

### Koncept Interfejsa

* Interfejs nije klasa, ali jeste skup *zahteva* za klase koje ih 
  implementiraju.
* Primer: `sort` metod klase `Arrays` obecava da ce sortirati objekte niza, 
  ali pod jednim uslovodom, da ti objekti pripadaju klasi koja implementira
  `Comparable` interfejs.
```java
public interface Comparable {
    int compareTo(Object other);
}
```
* Ovo znaci da svaka klasa koja implementira `Comparable` mora da ima
  implementiran metod `compareTo` deklarisan u `Comparable`.
  * Naravno `x.compareTo(y)` vraca negativnu vrednost, ako je `x` manje
    od `y`, 0, ako je `x` jednako `y`, ili pozitivnu vrednost ako je `x` vece
    od `y`.
* Svi metodu u interfejsu su `public`.
* Interfejs nikada nemaju instance polja.
* Do Java SE 8, metodi nikada nisu implementirani u interfejsu.
  * Ali to je moguce: staticni metodi i defailt metodi.
* Pretpostavimo da hocemo da sortiramo niz `Zaposleni`. 
  * `Zaposleni` moraju da *implementiraju* interfejs `Comparable`.
    1. Deklarisemo da clasa implementira dati interfejs
```java
        class Zaposleni implements Comparable`
```
    2. Definisemo sve metode interfejsa.
```java
        public int compareTo(Object otherObject) {
            Zaposleni drugi = (Zaposleni) otherObject;
            return Double.compare(plata. drugi.plata);
        }
```
```java
        // Bolji nacin:
        class Zaposleni implements Comparable<Zaposleni> {

            public int compareTo(Zaposleni drugi) {
                return Double.compare(plata. drugi.plata);
            }

        }
```

### Osobine Interfejsa

* Interfejs nije klasa pa sledeci kod proizvodi gresku:
```java
    x = new Comparable(); // Greska!!!
```
* Moguce je deklarisati interfejs promenljivu:
```java
    Comparable x;
```
* Ta promenljiva mora da referise na neki objekat koji implementira
  taj interfejs:
```java
    x = new Zaposleni(..);
```
* Moguce je koristiti `instanceof` da proverimo da li neki objekat 
  implementira neki interfejs.
* Postoje i hijerarhije interfejsa, pa je moguce naslediti neki interfejs.
* Instance mogu sadrzati konstante
  * Polja su automacki `public static final`, kao sto su metode `public`.
* Klase mogu da implementiraju *vise* interfejsa.


### Interfejs i Apstraktne Klase

* Zasto postoje interfejsi i apstraktne klase?
* Nije moguce naslediti vise apstraktnih klasa, dok je moguce implementirati
  vise interfejsa.
  * Java ne podrzava *visestruko nasledjivanje*.

### Staticki Metodi

* Od SE 8 moguce je imati staticke metode u interfejsu.
* Do sada je bilo zgodno imati posebno interfejs i klasu sa statickim 
  funkcijama, na primer: `Collection/Collections` ili `Path/Paths`.
* Te razdvajanje idalje postoji zbog odrzavanja koda, ali noviji programi
  imaju samo interfejs.

### Default Metodi

* Moguce je imati *default* implementaciju za interfejs metod. Taj metod
  mora imati `default` modifikator:
```java
    public interface Comparable<T> {

        default int compareTo(T other) { 
            return 0; 
        }

    }
```
* Postoje slucaji kada je ovo korisno!

### Rezolucija Default Metoda

* Sta se desi ako se isti metod definise kao default metod nekog interfejsa
  i kao metod superklase ili drugog interfejsa?
  1. Superklasa pobedjuje, ako superklasa pruza metod, default metod 
     sa istim imenom i parametrima se igrnorise. (*class win*)
  2. Interfejs sukob nastaje ako, superinterrfejs pruza default metod i drugi
     interfejs pruza metod istog imena i parametara (nije bitno da li default).
* Zbog sukoba ostavlja se programeru da ga resi, tako sto ce da pruzi
  taj isti metod u klasi koja nasledjuje te interfejse.

## Primeri Interfejsa

### Interfejs i Povrati Pozivi

* Povrati pozivi (engl. *callback*) opisuju akciju koja se desava kadgod
  se neki odredjeni dogadjaj desi.
  * Primer: Kada se pretisne neko dugme itd...

### `Comparator` Interfejs

* Ako hocemo da sortiramo stringove po duzini, nije moguce jednostavno
  zameniti implementaciju `compareTo` metoda u `String` klasi.
* Zbog toga postoji jos jedan metod `Arrays.sort` koji ima dva parametra
  prvi je niz, a drugi *comparator*, instanca klase koja implementira
  `Comparator` interfejs.
```java
    public interface Comparator<T> {
    }

    class Lenght Comparator implements Comparator<String> {
        
        public int compare(String first, String second) {
            return frist.length() - second.length();
        }

    }

    String[] names = { "Pera", "Ana", "Marko" };
    Arrays.sort(names, new LengthComparator());
```

### Kloniranje Objekara

* `Cloneable` interfejs pruza klasi siguran `clone` metod.
* Ako hocemo da *kopiramo* neki objekat, ali ne u smilu njegove reference
  nego hocemo da dabijemo novi objekat koji je istog stanja kao originalni
  koristimo `clone` metod.
* `clone` metod je `protected` metod klase `Object`, sto znaci da nije moguce
  jednostavno pozvati ga, tj. samo jedna klase moze da klonira samu sebe.
  * Ovo ima slila zato sto je metod `clone` implementira tako da da pravi
    duplikate polja. 
  * Ako je polje primitivni tip, kopiranje je ok
  * Ako je polje neki objekat, onda stvara samo novu referencu na 
    isti objekat, pa oni idelje dele informacije.
  * Ovo se naziva *plitko kopiranje*.
* Da li je vazno sto je kopiranje plitko?
  * Ako je podobjekat deljen izmedju originalnog i plitkog klona *imputabilan*
    tada je deljenje sigurno.
  * Ali u vecini slucaja oni su *mutabilni*, zbog toga se mora redefinisati
    `clone` metod da bi pruzao *duboko kopiranje*, tj. klonirao i 
    podobjekte.
* Za svaku klasu potrebno je odluciti da li je:
  1. Default `clone` dovoljno dobar.
  2. Default `clone` se moze zakrpiti pozivanje `clone` na mutabilni
     podobjekat.
  3. `clone` se ne sme pokusavati
* Za prvo ili drugi klasa mora:
  1. Implementirati `Cloneable` interfejs, i
  2. Redefinisati `clone` metod sa `public` pristupajucim modifikatorom.
* U ovom slucaju interfejs sluzi samo kao labela, koja pokazuje da dizajner
  klase poznaje koncept kloniranja.
```java
    public Zaposleni clone() throws CloneNotSupportedException {
        Zaposleni cloned = (Zaposleni) super.clone();
        // kloniramo mutabilna polja kojih trenutno nema
        return cloned;
    }
```
* Da li treba implementirati `clone` u sopstvenim klasama? 
  * Ako nam treba duboko kloniranje, onda verovatno treba.
  * Neki misle da se `clone` treba izbegavati, ali dobijamo slicne probleme
    ako probamo da implementiramo nas metod za kloniranje.

## Lambda Izrazi

### Zasto lambda?

* Lamda izraz je blok koda koji se moze slati negde da bi se izvrsavanje 
  odlozilo, ili izvrsi jednom ili vise puta.
* Dugo se cekalo da bi se ovo na kraju implementiralo u javi. Nije bilo
  pitanje da li ce se to desiti, nego kako ce se implementirati.

### Sintaksa Lambda 

* Za primer sortiranje od malopre saljemo kod koji proverava da li je 
  neki string kraci od nekog drugog stringa, tj. racunamo:
```java
  (String first, String second)
    -> first.length() - second.length()
```
* Kod koji se dobija se naziva *lambda izraz*, koji je jednostavno blok koda,
  zajedno sa specifikacijom promenljivih koje se koriste.
* Pre mnogo godina, Alonzo Cerc je hteo da formalizuje sta znaci da
  matematicka funkcija bude efikasno izracunata (sa druge strane postoje
  funkcije za koje se zna da postoje, ali niko ne zna kako da izracuna 
  njihove vrednosti). Koristio je grcko slovo lambda za parametre.
  * Zasto lambda? Pa video je ^ oznaku koja oznacava slobodnu promenljivu,
    pa se bio inspirisan za veliko Lambda, koje je onda postalo malo lambda.
* Ako imamo komplikovaniji izraz koristimo `{}` i `return`.
```java
    (String first, String second) -> {
        if (first.length() < second.length()) return -1;
        else if (first.length() > second.length()) return 1;
        else return 0;
    }
```
* Ako nema parametre moze jos uvek se koriste `()`.
```java
    () -> { for (int i = 100; i >= 0; i--) System.out.println(i); }
```
* Moguce je izostaviti tip parametra ukoliko se on nasledjuje.
* Ako ima samo jedan parametar moguce je izostaviti zagrade `()` i/ili `{}`

### Funkcionalni Interfejsi

* Moguce je pruziti lambda izraz kadgod je objekat interfejsa sa jednim
  apstraktnim metodom ocekivan. Takvi interfejsi se nazivaju
  *funkcionalni interfejsi*.
* Za demonstraciju konverzija u funkcionalni interfejs, razmotrimo
  `Arrays.sort` metod.
  * Za drugi parametar oceju se instanca od `Comparator` interfejsa sa 
    jednim metodom.
```java
    Array.sort(names, (first, second) -> first.length() - second.length()) 
```
* Primamljivi su zato sto su jednostavi i eleganti, i jedino je moguce
  koristiti konverziju u funkcionalne interfejse sa lambda izrazima.

### Reference metoda

* Nekada postoji metod koji nosi odredjenu akciju koji zelimo da prosledimo
  na nekom drugom delu koda.
* Pretpostavimo da hocemo da ispisujemo dogadjaj kad god se dogodi timer
  dogadjaj.
```java
    Timer t = new Timer(1000, event -> System.out.println(event));
    // Ekvivalentne linije
    Timer t = new Timer(1000, System.out::println); 
```
* Druga linija koristi izraz koji se naziva *referenca metoda* koji je
  ekfivalentan lambda izrazu.
* Sortiranje bez obracanja paznje na velika i mala slova:
```java
    Array.sort(strings, String::compareToIgnoreCase);
```
* Postoje 3 slucaja:
  1. *objekat`::`instancaMetode*
  2. *Klasa`::`statickaMetoda*
  3. *Klasa`::`instancaMetode*
* Prva dva su ekvivalentna lambda izrazu koji pruza parametre metodi.
* U trecem, nad prvim parametrom se poziva metod, dok su ostali parametri.
  * moguce je koristiti `this` i `super`: *`super::`instancaMetode*.

### Reference Konstruktora

* Referenca konstruktora je slicna referenci metoda, samo sto je ime
  metoda `new`. Primer: `Zaposleni::new``.

### Doseg Promenljivih

* Razmotrimo primer:
```java
    public static void repeatMessage(String text, int delay) {
        ActionListener listener = event -> {
            System.out.printf("%s\n", text);
            Toolkit.getDefaultToolkit().beep();
        };
        new Timer(delay, listener).start();
    }
```
* Kako lambda izraz zna za promenljivu `text`.
* Lambda izraz ime 3 dela:
  1. Blok koda
  2. Parametre
  3. Vrednosti za `slobodne` promenljive, tj. promenljive koji nisu paremetri
     i nisu definisane u bloku.
* U nasem slucaje `text` je slobodna promenljiva.
* Moramo cuvati vrednosti tih promenljivih, tj. kazemo da su takve vrednosti
  *uhvacene* lambda izrazom.
* Moguce je koristiti samo promenljive cije se vrednosti ne menjaju, tj.
  samo imputabilne promenljive kao slobodne promenljive.
  * Bilo koje uhvacene promenljive u lambda izrazu moraju biti *efektivno
    finalne*.
* Telo lambda izraza ima *isti doseg kao i udjezdeni blok*.
  * Nije moguce imati dve lokalne promenljive sa istim imenom.
* Kada se koristi `this` u lambda izrazu, `this` referise na parametar
  metoda koji se stvorio lambda.

### Procesiranje Lambda Izraza

* Pogledajmo sada kako se pisu metodi koji mogu da koriste lambda izraze.
* Poenta lambda izraza je *drugacije izvrsavanje* neke metode:
  * Izvrsavanje koda u zasebnoj niti.
  * Izvrsavanje koda vise puta.
  * Izvrsavanje koda na odredjenom mestu u algoritmu. (cmp za sort..)
  * Izvrsavanje koda kada se nesto desi. (kada neko pretisne dugme..)
  * Izvrsavanje koda samo kada je neophodno.
* Pretpostavimo da hocemo da ponavljamo nesto:
```java
    public static void repeat(int n, Runnable action) {
        for (int i = 0; i < n; i++) {
            action.run();
        }
    }

    public static void main (String[] args) {
        repeat(10, () -> System.out.printf("Hello!\n"));
    }
```
* Moramo izavrati funkcionalni interfejs iz Java API. U ovom slucaju
  koristimo `Runnable` interfejs.
  * telo lambda izraza se izvrsava kada se pozove `action.run()`.

### Nesto jos o Komparatorima

* `Comparator` interfejs ima puno zgodnih statik metoda za uporedjivanje.
  * Oni se koriste sa lambda izrazima.
```java
    // Uporedjujemo osobe leksikografski po imenu.
    Arrays.sort(people, Comparator.comparing(Person::getName));
    // Uporedjujemo osobe leksikografski po prezimenu pa po imenu.
    Arrays.sort(people, Comparator.comparing(Person::getLastName)
                                  .thenComparing(Person::getFirstName));
    // Uporedjivanje po duzini imena.
    Arrays.sort(people, Comparator.comparingInt(p -> p.getName().length()));
```

## Unutrasnje Klase

* *Unutrasnja klasa* je klase koja se definise unutar druge klase. Zasto?
  * Metodi unutrasnje klase mogu da pristupe podacima iz desega u kome
    su definisane, zajedno sa privatnim podacima.
  * Unutrasnje klase mogu biti sakrivene od drugih klasa u istom paketu.
  * *Anonimne* unutrasnje klase su zgodne kada hocemo da definisemo
    callback bez pisanja puno koda.

### Koriscenje Unutrasnjih Klasa za Pristup Stanja Objekata

```java

class TalkingClock {

    private int interval;
    private boolean beep;

    public TalkingClock(int interval, boolean beep) {
        this.interval = interval;
        this.beep = beep;
    }

    public void start() {
        ActionListener listener = new TimePrinter();
        Timer t = new Timer(interval, listener);
        t.start();
    }

    public class TimePrinter implements ActionListener {
        // Unutrasnja klasa...

        public void actionPerformed(ActionEvent event) {
            System.out.printf("At beep time is: %s\n", new Date());
            if (beep) Toolkit.getDefaultToolkit().beep();
        }

    }

}
```
* `TimerPrinter` klasa nema instance polja ili promenljivu nazvanu `beep`.
  * Tacnije, `beep` referisa na polje `TalkingClock` objekta, koji kreira
    objekat `TimePrinter`.
* Tradicionalno metod moze jedino referisati na polja objekta nad kojim
  je pozvan.
* Metodi unutrasnje klase mogu da pristupe i svojim poljima i 
  poljima spoljasnjeg objekta koji je stvara.

### Specijalna Sintaksna Pravila za Unutrasnje Klase

* `OuterClass.this` je referenca na spoljasnji objekat.
* `spoljasnjiObjekat.new UnutrasnjaKlasa(parametri)` pozivanje konstruktora 
  unutrasnje klase.

### Lokane Unutrasnje Klase

* Moguce je definisati klase *lokalno u jednoj metodi*.
* Njihov doseg je samo doseg bloka metoda, tako da nema smisla koristiti
  `public` ili `private` modifikatore.

### Pristupanje Promenljiva iz Spoljasnje Metode.

* Lokalne klase imaju jos mogucnusti nad drugim unutrasnjim klasama.
  * Mogu pristupati i lokalnim promenljivama, ali one moraju biti `final`.
* Da bi razlotrili zbog cega promenljiva mora biti `final` posmatramo
  kontrolu toka pazljivije:
  1. Metoda je pozvana
  2. Unutrasnji objekat se kreira.
  3. Taj objekat se mozda prosledi nekom drugom objektu.
  4. Izlazi se iz funkcije (samim tim se brisu i lokalne promenljive).
  5. Kreirani objekat idalje postoji i poziva metod unutrasnje funkcije
     koja zahteva lokalnu promenljivu koja vise ne postoji.
* Zbog tih razloga promenljiva mora biti `final`. (Ne uvek zapravo...)

### Anonimne Unutrasnje Klase

* Ako hocemo da napravimo samo jedan objekat unutrasnje klase, ne moramo
  da joj dajemo ime. Te kase nazivamo *anonimne klase*.
```java
     public void start() {
        ActionListener listener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                System.out.printf("At beep time is: %s\n", new Date());
                if (beep) Toolkit.getDefaultToolkit().beep();
            }
        };
        Timer t = new Timer(interval, listener);
        t.start();
    }
```
* Generalno sintaksa je:
```java
    new SuperType(construction parametars) {
        // metodi unutrasnje klase i podaci
    }
```
* `SuperType` moze da bude interfejs, kao u nasem slucaju, tada je
  * unutrasnja klasa implementira taj interfejs
* `SuperType` moze da bude klase, tada
  * unutrasnja klasa nasledjuje tu klasu
* Anonimna klase ne moze imati konstruktor kako nema ima

### Staticke Unutrasnje Klase

* Nekada hocemo da unutrasnja klase jednostavno bude sakrivena u nekoj
  drugoj klase, ali bez instanciranja objekta spoljasnje klase.
  * To mozemo spreciti deklarisanje unutrasnje klase kao `static`.
* Tipican primer, racunanje minimalnih i maksimalnih vrednosti niza.
  * Umesto da racunamo min i max vrednost u posebnim metodama, mozemo da
    imamo jednu metodu koja racuna obe vrednosti.
    * Samim tim ustedjujemo na vremenu jer prolazimo jednom kroz ceo niz.
```java
class ArrayAlgorithms {

    public static class Pair {

        private double first;
        private double second;

        public Pair(double first, double second) {
            this.first = first;
            this.second = second;
        }

        public double getFirst() {
            return first;
        }

        public double getSecond() {
            return second;
        }

    }

    public static Pair minmax(double[] values) {
        double min = Double.POSITIVE_INFINITY;
        double max = Double.NEGATIVE_INFINITY;
        for (double v : values) {
            if (min > v) {
                min = v;
            }
            if (max < v) {
                max = v;
            }
        }

        return new Pair(min, max);
    }

}
```
* Verovatno je vec neki programer napravio klasu `Pair`, koja predstavlja, 
  na primer, par dva `int`a, ali nama zapravo treba par dve `double` vrednsoti.
  * Zato javna unutrasnja klase resava problem jer ona dobija ime 
    `ArrayAlgorithms.Pair`.
* Ali ne zelimo da pravimo instancu objekta `ArrayAlgorithms` da bi pristupili
  `Pair` objektu.
  * To nam omogucava `static`.

# Izuzeci, Tvrdnje i Logovanje

* Kada dodje do greske potrebno je:
  * Obavestiti korisnika o gresci
  * Sacuvati sve sto je do sada radjeno
  * Dozvoliti korisniku da stopira program
* Kada dodje do nekih gresaka java koristi *obradu izuzetaka*
  (eng. exception handling)

## Pristup Greskama

* Pretpostavimo da dodje do greske dok se izvrsava Java program.
* Ako se operacija ne moze zavrsiti zbog greske, program bi trebalo da se
  * vrati u sigurno stanje i omoguci korisniku da izvrsi komandu, ili
  * prepusti korisniku da sacuva podatke i da terminise program.
* Obrada izuzetaka treba da transferuje kontrolu od mesta gde desila greska
  do obrade greske koja ce se pozabaviti situacijom.
* Moguci problemi?
  * *Pogresan korisnicki unos*
  * *Greska sa uredjajem*
  * *Fizicka limitacija*
  * *Greska u kodu*
* Ako neka metoda ne moze da nadje resenje, tradicionalno je vracala -1, ili
  `null` sto ukazuje na gresku.
  * To nije moguce uvek nekada -1 moze da bude greska ali i potpuno korektan 
    izlaz metode.
  * Jedna mogucnost je `throw` koja baca objekat koji sadrzi informaciju
    o gresci. Tada metod ne vraca normalnu vrednost.
  * Kada se to desi program se ne nastavlja dalje nego trazi 
    *obradu izuzetaka* kako bi se pozabavio greskom.

### Klasifikacija Izuzetaka

* Izuzetak je uvek instanca klase izvedene iz `Throwable`.
* `Exception` i `Error` nasledjuju `Throwable`.
* `Error` opisuje unutrasnju gresku ili nedostatak resursa u Java runtime.
  * Ne mozemo nista sem da cekamo da izadje nova verzija koja resava
    taj problem.
* `Exception` se deli `RuntimeException` i `IOException`
* `RantimeException` nasledjuju problemi kao sto je
  * Lose kastovanje
  * Pristupanje van granica
  * Pristupanje null pokazivacu
* One koje ne nasledjuju `RuntimeException` su:
  * Citanje posle kraja fajla
  * Otvaranje fajla koji ne postoji
* Vazi pravilo: Ako je `RuntimeException` onda si *ti* kriv.
  * Pristupanje van granica, ili null pokazivacu moze da se zaustavi
    jednostavnim uslovom da li smo u granicama i da li tome sto pristupamo
    nije null.
  * Dok u slucaju otvaranja fajla koji ne postoji, ukoliko proverimo
    da li postoji pre otvaranja, moguce je da neko obrise fajl pre
    nego sto ga otvorima, pa to ne zavisi od nas (od koda) nego od okruzenja.
* Svi izuzeci koji nasledjuju klasu `Error` ili `RuntimeException` su
  *neprovereni* izuzeci.
* Svi ostali se nazivaju *provereni* izuzeci.
* Kompajler proverava da li smo prozili obradu izuzetaka za svaki
  provereni izuzetak.

### Deklarisanje Proverenog Izuzetka

* Java metod moze da izbaci izuzetak ako se susretne sa situacijom koju
  ne moze da obradi.
  * Metod nece vratiti nikakvu vrednosti, ali ce reci kompajleru o kakvoj
    se gresci radi.
* U deklaraciji metode ukazujemo da metod moze da izbaci izuzetak.
```java
    public FileInputStream(String name) throws FileNotFoundException
```
* Dobijamo `FileInputStream` ali takodje moze doci do greske, i to
  izbacivanje `FileNotFoundException`.
* Izuzetak se izbacuje u sledecim situacijama:
  * Pozivamo metod koji izbacuje provereni izuzetak.
  * Detektujemo gresku i izbacuje provereni izuzetak sa `throw` izrazom
  * Napravimo programsku gresku (a[-1] = 0)
  * Unutrasnja greska se desi u virtualnoj masini ili u runtime biblioteci.
* U prva dva slucaja, treba ukazati programerima koji koriste funkciju o
  mogucem izuzetku
* Slicno ne treba obavestavati da nasa funkcija nije dobra jer smo napravili,
  na primer `ArrayIndexOutOfBoundsException`. Kao i da je moguce doci
  do izuzetka koji se nasledjuje iz `Error`.
* Ukratko treba deklarisati sve *proverene* izuzetke koje funkcija moze da 
  izbaci.

### Kako Baciti Izuzetak

* Pretpostavimo da se nesto uzasno desilo. Imamo metod `readData`, koji
  cita iz fajla ciji je header obecao duzinu `1024`, ali
  imamo `EOF` nakon `892` karaktera. 
* Zbog toga biramo iz dokumentaciju odgovarajuceg naslednika `IOException`.
* Nakon trazenja nalazimo da je u nasem slucaju perfektan `EOFException`.
```java
    throw new EOFException(); // bacamo EOF izuzetak
```
* Ovaj izuzetak ima jos jedan konstruktor koji kao parametar sadrzi string
  koji moze da sadrzi korisne informacije o gresci, u nasem slucaju je to
```java
    throw new EOFException("Procitano: " + len); // bacamo EOF izuzetak
```
* Ako postoji klasa odgovarajuceg izuzetka:
  1. Nalazimo tu klasu
  2. Pravimo objekat te klase
  3. Bacamo ga

### Kreiranje Klasa Izuzetaka

* U slucaju da vec ne postoji odgovarajuca klasa za nas izuzetak, mozemo
  napraviti nasu klasu izuzetka.
* Dovoljno je naslediti je od neke klase izuzetka koji vec postoji:
```java
    class FileFormatException extends IOException
    {
        public FileFormatException() {}
        public FileFormatException(String gripe)
        {
            super(gripe);
        }
    }
```

## Hvatanje Izuzetaka

* Kada bacimo izuzetak, neki drugi deo koda treba da uhvati taj izuzetak.

### Hvatanje Izuzetka

* Ako dodje do izuzetka i on se ne uhvati program terminise.
* Za hvatanje izuzetka, postavlja se `try/catch` blok.
```java
    try {
        code
        ...
        code
    } catch (ExceptionType e) {
        // obrada izuzetka datog tipa
    }
```
* Ako unutar `try` bloka izbaci izuzetak, koji je istog tipa kao i 
  `ExceptionType` (naravno moze da bude njegov naslednik), onda se
  1. Preskace ostatak koda u `try` bloku
  2. Izvrsava se obrada u `catch` bloku
* Ako se unutar `try` bloka ne izbaci izuzetak, program preskace `catch` blok.
* Primer:
```java
    public static void read(String filename) throws IOException {
        InputStream in = new FileInputStream(filename);
        int b;
        while ((b = in.read()) != -1) {
            System.out.printf("%d\n", b);
        }
        in.close();
    }

    public static void main (String[] args) {
        try {
            read("test.txt");
        } catch(IOException e) {
            e.printStackTrace();
        }
    }
```
* Kako odrediti kada je dobro koristiti throw i odlagati obradjivanje greske,
  a kada je dobro obraditi tu gresku?
  * Generalno bolje je *uvek* obraditi gresku ako *znamo kako*, ako to nije 
    slucaj bolje je odlagati koriscenjem `throw`.
* Postoji jedan izuzetak: Ako redefinisemo metod superklase koja ne izbacuje
  ni jedan izuzetak, tada moramo obraditi sve izuzetke u toj metodi, jer
  nije moguce menjati deklaraciju metode superklase.

### Hvatanje Vise Izuzetaka

```java
    try {
    } catch (FileNotFoundException e | UnknownHostException e) { // nadovezivanje od SE7
        System.out.printf("%s", e.getClass().getName());
    } catch (IOException e) {
        System.out.printf("%s", e.getMessage());
    }
```

### Ponovno Bacanje i Lancanje Izuzetaka

* Moguce je baciti izuzetak u `catch` bloku.
  * Obicno ovo se radi ako hocemo da promenimo tip izuzetka.

### Finally Blok

* Kada neki deo koda u `try` bloku izbaci izuzetak, prestaje procesiranje
  ostatka koda u bloku. Ovo moze da bude problem.
  * Sta ako je neki deo koda pre izbacivanje izuzetka, zauzeo neki resurs,
    taj resurs mora biti oslobodjen kasnije, ali kako smo preskocili
    ostatak koda koji to radi moramo nekako pruziti mogucnost za to.
* Java ima resenje u vidu `finally` bloka.
  * Taj blok se izvrsava uvek bez obzira na to da li se izbacio izuzetak
    ili nije.
```java
InputStream in = new FileInputStream(...);
try {
    // 1
    // moguce je izbaciti izuzetak
    // 2
} cathc(IOException e) {
    // 3
    // obrada greske
    // 4
} finally {
    // 5
    in.close();
}
// 6
```
1. Nemamo izuzetak:
  * Izvrsi se ceo `try` blok, pa se izvrsi `finally` blok.
  * Prolazimo kroz 1, 2, 5, 6.
2. Izbaci se izuzetak koji se hvata u `catch` bloku.
  * Izvrsi se sve u `try` bloku dok ne dodje do izbacivanja greske, ostak se
    preskace, pa se izvrsava `catch` blok, i na kraju `finally`.
  * Prolazimo kroz 1, 3, 4, 5, 6.
3. Izbaci se izuzetak koji se ne hvata u `catch` bloku.
  * Izvrsi se sve u `try` bloku dok ne dodje do izbacivanja greske, ostak se
    preskace, pa se izvrsava samo `finally`, te se program terminira.
  * Prolazimo kroz 1, 5.
* Mozemo koristiti `finally` blok bez `catch` bloka.

### Try-with-Resources izraz

* Sta ako kod u `finally` bloku izbaci gresku?
  * Moramo imati ugnjezdene blokove, ali na srecu:
```java
// Otvori resurse
try {
    // radi sa resursima
} finally {
    // zatvori resurse
}
```
* Java SE7 pruza zgodan izraz , ako pri tome resursi implementiraju 
  `AutoClosable` interfejs.
  * tj. imaju samo jedan metod `void close() throws Exception`.
* Tipican primer:
```java
try (Scanner in = new Scanner(new FileInputStream("text.txt")), "UTF-8") {
    while (in.hasNext()) {
        System.out.println(in.next());
    }
}
```
* Nije bitno da li dodje do izbacivanje izuzetka ili ne `in` se svakako
  zatvara.

## Hintovi za Koriscenje Izuzetaka

1. *Obradjivanje izuzetaka ne sme zameniti jednostavnu proveru*.
  * Bolje je proveriti da li je stek prazan pre skidanja sa vrha nego hvatati 
    hvatati gresku ako pokusamo da skinemo sa vrha, a stek prazan.
2. *Ne koristiti `try/catch` za svaku liniju, vec obuhvatiti vise linija
   jednim `try/cathc` blokom.*
3. *Koristi dobro hijerarhiju izuzetaka*
4. *Ne prigusuj greske samo zato sto kompajler kaze da trebas da obradis gresku.*
5. *Ne koristi glupe pormenljive kao povratne greske.*
6. *Odlaganje gresaka nije ne znanje obrade, vec je pozeljno ukoliko nije
   poznato kako obraditi tu gresku u datom trenutku.*

## Tvrdnje

## Logovanje

# Generiko Programiranje

## Zasto genericko programiranje

* *Genericko programiranje* znaci pisanje koda koji moze da se iskoristi za
  objekte drugacijih tipova.

### Prednosti Tipiziranih parametara

* Pre generickih klase u Javi takvo programiranje se postizalno 
  *nasledjivanjem*.
```java
public class ArrayList {
    privete Object[] elementData;
    ...
    public Object get(int i) { ... }
    public void add(Object o) { ... }
}
```
* Dva problema:
  * Kastovanje je neophodno.
    * Ako koristimo `get` moramo kastovati iz `Object` u zeljni tip.
  * Nema provere gresaka.
    * Ako koristimo `add` mozemo da ubacimo bili koji tip.
* Resenje nudi genericko programiranje i to *tipizorani parametri*.
  * `ArrayList` moze da ima svoj sopstveni tip parametara koji ukazuje 
    na tip elemenata
```java
    ArrayList<String> files = new ArrayList<String>();
```
  * Slicno nema potrebe za kastovanjem jer `get` ne vraca `Object` vec
    dati objekat datog tipa (u gorenjem primeru to je `String`).
  * Takodje, docice do greske ako se pozove `add` sa nekim parametrom
    koji nije `String` u nasem slucaju.

### Ko hoce da bude genericki programer?

* Lako je koristiti genericke klase kao sto su `ArrayList`. 
* Tesko je implementirati genericku klasu. Koliko tesko?
  * Primer hocemo da dodamo sve iz `ArrayList<Menadzer>` u 
    `ArrayList<Zaposleni>` i to koriscenjem `addAll`, sto je ok ali nije 
    ok raditi obrnuto.
  * Postoji koncept `wildcard type` koji resava ovaj problem.
* Postoje 3 nivoa generickog programiranja:
  1. Osnovni: Samo koristimo genericke klase, bez znanja kako one rade.
  2. Srednji: Ako nesto krene naopako moramo nauciti nesto o generickim klasama.
  3. Napredni: Implementiramo sopstvene genericke klase i metode.

## Definisanje Jednostvane Genericke Klase.

* *Genericka klase* je klasa sa jednom ili vise promenljivih tipova.
* Konstruisemo jednostavu genericku klase `Par`.
```java
public class Par<T> {

    private T prvi;
    private T drugi;

    public Par() {
        this.prvi = null;
        this.drugi = null;
    }

    public Par(T prvi, T drugi) {
        this.prvi = prvi;
        this.drugi = drugi;
    }

    public T getPrvi() {
        return prvi;
    }

    public T getDrugi() {
        return drugi;
    }

    public void setPrvi(T prvi) {
        this.prvi = prvi;
    }

    public void setDrugi(T drugi) {
        this.drugi = drugi;
    }

}
```
* Genericke klase moguce da imaju i vise od dve promenljive tipa.
  * `public class Pair<T, U> { ... }`
* Promenljiva tipa se koristi kroz definiciju klse.
* *Instanciranjem* generickog tipa vrsi se supstitucija promenljivih tipova.
  * Instanciranjem: `Pair<String>` dobijamo:
```java
    // polja postaju
    private String prvi;
    private String drugi;

    // konstruktori postaju
    Par<String>()
    Par<String>(String, String)

    // metodi postaju
    String getPrvi()
    String getDrugi()
    void setPrvi(String)
    void setDrugi(String)
```
* Ukratko genericke klase su kao uputstvo za pravljenje obicnih klasa.

## Genericke Metode

* Moguce je i definisati genericke funkcije
```java
class Algoritmi {
    public static <T> T getSrednji(T... a) {
        return a[a.length / 2];
    }
}
```
* Pozivanje generickih metoda je jednostavno:
```java
// Od 3 Pere dobijamo drugog Peru
String srednji = Algoritmi.<String>getSrednji("Pera", "Pera2", "Pera3");
```

## Ogranicenja za Promenljive Tipove

* Razmotrimo sledeci primer:
```java
    public static <T> T min(T[] a) {
        if (a == null || a.length == 0) return null;
        T m = a[0];
        for (int i = 1; i < a.length; i++) {
            if (m.compareTo(a[i]) > 0) {
                m = a[i];
            }
        }
        return m;
    }
```
* U ovom slucaju kompajler upozorava na gresku da `compareTo` mozda ne postoji
  za tip `T`.
  * Resenje je restrikcija `T` na klase koje implementiraju `Comparable`
    interfejs.
* Moguce je dati ogranicenje promenljivoj tipa T kao
```java
    public static <T extends Comparable> T min(T[] a) ...
```
* Kompajler i dalje ukazuje na gresku, ali to resavaju wildcard tipovi.
* Mozda se pitate zvog cega koristimo kljucno rec `extends` umesto
  kljucne reci `implements` jer je `Comparable` interfejs.
  * Ovo znaci da je `T` *podtip* ogranicenog tipa.
  * Rec `extends` je izabrana zato sto vise odgovara reci *pod-* nego rec
    `implements`.
* Moguce je ograniciti promenljivu na sa vise tipova
```java
    T extends Comparable & Serializable
```

## Genericki Kod i Virtualna Masina

### Brisanje Tipova

* Kada se definise genericki tip, odgovarajuci *sirovi* tip se odmah pruza.
* Tip promenljive se *brise* i zamenjuje za svojim ogranicavajucim tipom.
  (`Object` tipom ako promenljivi tip nema ogranicenje).
  * Na primer `Par<T>` postaje:
```java
public class Par<Object> {

    private Object prvi;
    private Object drugi;

    public Par() {
        this.prvi = null;
        this.drugi = null;
    }

    public Par(Object prvi, Object drugi) {
        this.prvi = prvi;
        this.drugi = drugi;
    }

    public Object getPrvi() {
        return prvi;
    }

    public Object getDrugi() {
        return drugi;
    }

    public void setPrvi(Object prvi) {
        this.prvi = prvi;
    }

    public void setDrugi(Object drugi) {
        this.drugi = drugi;
    }

}
```
* Da smo implementirali `Par<T extends Comparable>` dobili bi slicno samo
  svuda gde je `Object` nalazilobi se `Comparable`.

### Prevodjenje Generickih Izraza

* Kada program pozove genericki metod, compajler doda castovanje nakon 
  sto se povratni tip obrise.
```java
    Par<Zaposleni> drugari = ...;
    Zaposleni drug = drugari.getPrvi();
```
* Brisanjem tipa za `getPrvi()` metod vraca `Object`. Kompajler ubacuje
  kastovanje u Zaposleni, tj. dolazi do dve instrukcije:
  1. Pozove se sirovi metod `Par.getPrvi()`.
  2. Kastuje se povratna vrednost `Object` u tip `Zaposleni`.

### Prevodjenje Generickog Metoda.

* Brisanje se takodje desava i za genericke metode.
```java
    public static <T extends Comparable> T min(T[] a)
    // dobijamo sledece:
    public static Comparable min(Comparable[] a)
```
* Ovo dovodi do nekih komplikacija...#TODO
* Ukratko:
  * Nemamo genericke klase u virtualnom masini, samo obicne klase i metode
  * Svi tipovi parametara su zamenjeni njihovim ogranicenjima.
  * Premostivi metodi su sintetizovani da ocuvaju polimorfizam.
  * Kastovanje se dodaje da ocuva sigurnost tipa.

### Pozivanje Legacy Koda

## Restrikcije i Limitacije

* Vecinja njih je posledica brisanja tipova.

### Tip Parametara Ne Biti Instanciran sa Primitivinm Tipovima

* Nije moguce zameniti primitivni tip za tip parametra.
  * Ne postoji `Par<int>`, vec samo `Par<Integer>`.
* Razlog: Brisanje tipova
  * Naime nije moguce dodeliti `Object` tipu `int` vrednost.

### Ispitivanje Tipova za Vreme Izvrsavanja Radi Samo sa Sirovim Tipovima

```java
    if (a instanceof Par<String>) // Greska!
    if (a instanceof Par<T>) // Greska!
    Par<String> p = (Par<String>) a; // Upozorenje!

    Par<String> stringPar = ... ;
    Par<Zaposleni> zaposleniPar = ... ;
    if (stringPar.getClass() == zaposleniPar.getClass()) // uvek vazi
```

### Nije Moguce Kreiranje Nizova sa Parametrizovanim Tipom

```java
    Par<String>[] tabela = new Par<String>[10]; // Greska!
```

### Varargs Upozorenja

* Razmotrimo sledeci problem:
  * Prosledjivanje instance generickog tipa metodi sa promenljivim brojem
    argumenata.
```java
    public static <T> void addAll(Collection<T> coll, T... ts) {
        for (t : ts) {
            coll.add(t);
        }
    }

    Collection<Par<String>> tabela = ... ;
    Par<String> par1 = ... ;
    Par<String> par2 = ... ;
    addAll(tabela, par1, par2);
```
* Ovde se pravi niz `Par<String>` sto nije moguce.
* Ali na srecu ovde dobijamo samo upozoronje koje moze da se prigusi sa:
  `@SuppressWarnings("unchecked")` anotacijom na poziv `addAll`.
  * Ili anotacijom metoda `addAll` sa `@SafeVarargs`.

### Nije Moguce Instanciranje Promenljivih Tipova

```java
    public Par() { prvi = new T(); drugi = new T(); } // Greska! (new Object())
    Par<String> p = Par.napraviPar(String::new) // Ovo moze

    // pritom  je funkcija definisana kao
    public static <T> Par<T> napraviPar(Supplier<T> constr) {
        return new Par<>(constr.get(), constr.get());
    }
```

### Nije Moguce Konstruisati Genericki Niz

```java
    // Greska!!!
    public static <T extends Comparable> T[] minmax(T[] a) {
        T[] mm = new T[2]; ...
    }
```

### Promenljivi Tipovi Nisu Validne u Statickom Kontekstu Genericke Klase

```java
    public static T name; // Greska!!!
    public static T getName() { // Greska!!!
        if (name == null) {
            // konstruisi novu instanuce od T
        }
        return name;
    }
```

### Nije Moguce Baciti ili Uhvatiti Instance Genericke Klase

```java
    public class Problem<T> extends Exception { /*...*/ } // Greska!!!
```
```java
    public static <T extends Throwable> void doWork(T t) throws T { // OK
        try {
            // do work
        } cathc (Throwable e) { // Ovde ne sme da bude (T e)
            t.initCause(e);
            throw t;
        }
    }
```

### Budeti Svsni Sudaranja posle Brisanja

* Ilegalno je kreirati uslov koji stvara sudar kada se genericki tip obrise.
```java
public class Par<T> {
    public boolean equals(T vrednost) {
        return prvi.equals(vrednost) && drugi.equals(vrednost);
    }
}

// Posle brisanja
boolean equals(Object); // Ovaj metod vec postoji u Object klasi!!!
```
* Za podrzavanje prevodjenja brisanje uvodimo restrikcije koje klase ili
  promenljivi tipovi onemogucavaju da budu u isto vreme podtip dva tipa
  interfejsa koji su razlicitih parametara. STA?
```java
class Zaposleni implements Comparable<Zaposleni> { /* ... */ }
class Menadzer extends Zaposleni implements Comparable<Menadjer> { /* ... */}
// Ovo je greska!!!
```
* U Ovom slucaju `Menadzer` nasledjuje i `Comparable<Zaposleni>` i
  `Comparable<Menadzer>`, koji su razlicitih parametara istog interfejsa.
  
## Pravilo Nasledjivanja za Genericke Tipove

* Posmatramo klasu, podklasu i njihove parove:
  * `Zaposleni`, `Menadzer`. Da li je `Par<Menadzer>` podklasa od 
    `Par<Zaposleni>`? Odgovor je Ne?
```
    Zaposleni   Par<Zaposleni>
       ^
       |     Oni nemaju nikakvu relaciju
       |
    Menadzer    Par<Menadzer>
```
* Ali genericke klase mogu da prosire ili implementiraju druge genericke klase.
  * Na primer: `ArrayList<T>` implementira interfejs `List<T>`.
```
                   interfejs
         --------->   List  <--------
        /           (sirov)          \
        |              ^             |
    interfejs          |         interfejs
      List             |           List
    <Menadzer>         |        <Zaposleni>
        ^              |             ^ 
        |          ArrayList         |
        |       /-> (sirov) <-\      |
        |      /               \     |
        |     /                 \    |
     ArrayList                   ArrayList
     <Menadzer>                 <Zaposleni>
        ^                            ^
        |                            | 
        \------nemaju relaciju-------/
```

## Wildcard Tipovi

### Koncept Wildcard Tipova

* Wildcard tip moze da varira.
```java
    Par<? extends Zaposleni>
```
* Kako koristiti ovo?
```java
public static void printDrugove(Par<Zaposleni> p) {
    Zaposleni prvi = p.getPrvi();
    Zaposleni drugi = p.getDrugi();
    System.out.println(prvi.getName() + " I " + dugi.getName());
}
```
* Ako pozovovemo ovu funkciju sa argumentom tipa `Par<Menadzer>`, dobicemo
  gresku, ovo mozemo jednostavno da resimo koriscenjem wildcard tipa.
```java
public static void printDrugove(Par<? extends Zaposleni> p) {
```
```
               Par
             (sirov)
                ^
                |
                |
               Par
       <? extends Zaposleni>
                ^
                |
                |
    --------------------------
    |                        |
   Par                      Par
<Menadzer>              <Zaposleni>
```

### Supertip Ogranicenje za Wildcards

* Pored gornjeg ogranicenja, wildcard imaju specijalno *supertip ogranicenj*
  * Ogranicenje za sve super tipove od Menadzer.
```java
    ? super Menadzer
```

### Wildcards bez ogranicenja

* Postoje i wildcard bez ogranicenja: `Par<?>`
  * Tip `Par<?>` ima sledece metode:
```java
    ? getPrvi()
    void setPrvi(?)
```
* Povratna vrednost `getPrvi` moze se dodeliti *samo* `Object`.
* `setPrvi` se *nikada* ne moze pozvati, ni sa `Object` parametrom.

### Wildcard Capture

## Refleksija i Genericke klase

* Refleksija omogucava analizu objekata u izvrsavanju. Ako su objekti
  instance genericke klase nije moguce dobiti puno informacija o 
  generickim tipovima parametara zato sto bivaju obrisani.

### Genericka Klasa `Class`

* `String.class` je zapravo ovjekat klase `Class<String>`.
```java
T newInstance() // vraca instancu klase
T cast(Object obj) // vraca dati objekat u tipu T ako je on podtip od T
T[] getEnumConstants() // vraca null ako nije enum klasa ili 
                       // niz enumerisanih vrednosti koje su tipa T
Class<? super T> getSuperclass()
Constructor<T> getConstructor(Class... parameterTypes)
Constructor<T> getDeclaredConstructor(Class... parameterTypes)
```

### Koriscenje `Class<T>` Parametara za Uparivanje Tipova

```java
public static <T> Par<T> napraviPar(Class<T> c) throws InstantiationException,
    IllegalAccessException
{
    return new Par<>(c.newInstance(), c.newInstance());
}
```

### Genericki Tip Informacija u Virtualnoj Masini

// TODO

# Kolekcije

* Kolekcije podrazumevaju strukture podataka koje su potrebne za ozbiljno
  programiranje.

## Java Framework Kolekcija

### Odvajanje Kolekcija Interfejsom i Implementacijom

* Posmatrajmo sturukturu *red*.
* *Interfejs reda* sadrzi samo odgovarajuce metode.
```java
public interface Red<E> {
   void dodaj(E element);
   E izbaci();
   int velicina();
}
```
* Implementacija ovog intefejsa moze se uraditi na vise nacina.
  * Primer: `NizRed, ListaRed`.
* Kada se korisit nije nam bitna implementacija, dovoljno je da znamo
  koje sve metode odabrana kolekcija podrzava.
```java
    Red<Potrosac> potrosaci = new NizRed<>();
    potrosaci.dodaj(new Potrosac("Pera"));

    Red<Potrosac> potrosaci = new ListaRed<>();
    potrosaci.dodaj(new Potrosac("Pera"));
```

### `Collection` Interfejs

```java
   public interface Collection<E> {
   boolean add(E element);
   Iterator<E> iterator();
   . . .
}
```
* `add` metod dodaje element u kolekciju i vraca tu ako je element dodat.
* `iterator` metod vraca objekat koji implementira `Iterator` interfejs.

### Iteratori

```java
public interface Iterator<E> {
   E next();
   boolean hasNext();
   void remove();
   default void forEachRemaining(Consumer<? super E> action);
}

Collection<String> c = . . .;
Iterator<String> iter = c.iterator();
while (iter.hasNext()) {
   String element = iter.next();
   // iteriranje kroz sve elemente kolekcije
}

// foreach petlja
for (String element : c) {
    // iteriranje kroz sve elemente kolekcije
}
```

### Genericke Korisne Metode

* `Collection` i `Iterator` interfejsi su genericki, sto znaci da mozes
  napisati bili koji korisne metode koji operisu na bili kojoj kolekciji.
```java
public static <E> boolean contains(Collection<E> c, Object obj) {
   for (E element : c)
      if (element.equals(obj))
        return true;
   return false;
}
```

### Interfejsi u Kolekcijskom Frameworku

* Fundamentalni interfejsi: `Collection` i `Map`.
* Kod mapa umesto `add` imamo `V put(K key, V value)`.
* Dobijanje vrednosti elementa kljucem `key` koristimo `V get(key)`.
* `List` je *uredjena kolekcija*.
  * Mozemo da pristupamo elementima sa iteratorom ili po indeksu.
```java
void add(int index, E element)
void remove(int index)
E get(int index)
E set(int index, E element)
 ```
* `ListIterator` interfejs je subinterfejs od `Iterator`.
* `Set` interfejs je slican `Collection` interfesju.
  * `add` metod ne dodaje duplikate.
  * `equals` metod proverava da li dva skupa imaju iste elemente
    ali ne moraju da budu u istom redu.
  * `hashCode` metod koji daje isti hes kod ako su elementi dva skupa isti.
* `SortedSet` i `SortedMap` interfejs pridruzuju comparator objekat
  koji se korisit za sortiranje.
* `NavigaleSet` i `NavihableMap` sadrzi dodatne metode za trazenje i
  obilazenje u sortiranim skupovima i mapama.
  * `TreeSet` i `TreeMap` implementiraju ove interfejse.

## Konkretne Kolekcije

### Linked Lists

* Povezane liste `LinkedList` su zapravo dvostruko povezane liste.
  * Zbog toga brisanje elementa kod ovih lista je efikasno.
* Povezane liste su *uredjena kolekcija*.

### Array Lists

* `ArrayList` implementira interfejs `List` tako da ima random pristup
  sa `get` i `set` metodama.
* `ArrayList` enkapsulira dinamicki alociran niz objekata.

### Hash Sets

* Nekada nam je potreban direktan pristup nekom elementu ali ne zelimo
  da imamo uredjenu kolekciju.
* *Hash table* je struktura podataka koja nam treba.
* Za svaki objekat racuna se `hashCode`.
* U Javi has tabele su implementirane kao nizovi povezane liste.
  * Svaku listu nazivamo korpa.
  * Ostalo je standardno...

### Tree Sets

* `TreeSet` je slicna `HashSet` sem sto su u njoj u uredjnoj kolekciji.
* Implementacija `TreeSet` koristi *crveno-crna stabla*.

### Queues i Deque

* `Queue<E>`
  * `boolean add(E element)`
  * `boolean offer(E element)`
  * `E remove()`
  * `E poll()`
  * `E element()`
  * `E peek()`
* `Deque<E>`
  * `void addFirst(E element)`
  * `void addLast(E element)`
  * `boolean offerFirst(E element)`
  * `boolean offerLast(E element)`
  * `E removeFirst(E element)`
  * `E removeLast(E element)`
  * `E pollFirst(E element)`
  * `E pollLast(E element)`
  * `E getFirst(E element)`
  * `E getLast(E element)`
  * `E peekFirst(E element)`
  * `E peekLast(E element)`

### Priority Queues

* `PriorityQueue` implementira *heap*.
* `add` i `remove` metode.
  * `PriorityQueue()`
  * `PriorityQueue(int initalCapacity)`
  * `PriorityQueue(int initalCapacity, Comparator<? super E> c)`

## Mape

### Osnovne Map Operacije

* Fundamentalne implementacija za mape: `HashMap` i `TreeMap`.
  * Obe implementiraju `Map` interfejs.
* `HashMap` se koristi ako hocemo da imamo brzi pristup elementima
  pomocu kljuca bez uredjenja, dok `TreeMap` radi isto ali sa uredjenjem.
* `Map`
  * `V get(Object key)`
  * `default V getOrDefault(Object key, V defaltValue)`
  * `V put(K key, V key)`
  * `void putAll(Map<? exrends K, ? extends V> entries)`
  * `boolean containsKeys(Object key)`
  * `boolean containsValue(Object value)`

### Azuriranje Entiteta Mape

```java
counts.put(word, counts.getOrDefault(word, 0) + 1);
// Moze bolje
counts.putIfAbsent(word, 0);
counts.put(word, counts.get(word) + 1);
// Moze bolje
counts.merge(word, 1, Integer::sum);
```

### Pregled Mape

* `Map` interfejs nije kao `Collection`, tj. nije moguce iterirati kroz
  `Map` objekat.
* Za resenje ovog problema imamo metode:
```java
    Set<K> keySet()
    Collection<V> values()
    Set<Map.Entry<K, V>> entrySet()
```

### Weak Hash Maps

* `WeakHashMap` je dizajnirana da resi problem:
  * Sta se desi sa kljucevima koji se ne koriste nigde u programu.
* `WeakHashMap` koristi *slabe reference* za cuvanje kljuceva.
* `WeakReference` objekat cuva referencu na drugi objekat, u ovom slucaju,
  na hes tabelu.
  * Normalno ako nemamo referencu na neki objekat garbage collector 
    jednostavno oslobodi objekat, ali ako je objekat dostizan *jedino* 
    preko `WeakReference`, garbage collector, takodje, oslobodi objekat.

### Linked Hash Sets i Maps

* `LinkedHashSet` i `LinkedHashMap` klase pamte red kojim se elementi
  dodati u mapu.

### Enumerisani Sets i Maps

* `EnumSet` je efikasna implementacija skupa sa elementima koji pripadaju
  nekom enumerisanom tipu.
  * Implementiran je jednostavno kao sekvenca bitova. Bit je 1 ako
    je odredjena vrednost u skupu.
```java
enum Weekday { MONDAY, TUESDAY, WEDNESDAY, THURSDAY, FRIDAY, SATURDAY, SUNDAY };
EnumSet<Weekday> always = EnumSet.allOf(Weekday.class);
EnumSet<Weekday> never = EnumSet.noneOf(Weekday.class);
EnumSet<Weekday> workday = EnumSet.range(Weekday.MONDAY, Weekday.FRIDAY);
EnumSet<Weekday> mwf = EnumSet.of(Weekday.MONDAY, Weekday.WEDNESDAY, Weekday.FRIDAY);
```

## Pregledi i Wrapperi

## Algoritmi

## Legacy Kolekcije
