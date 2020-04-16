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

## Konstrukcije Objekta

## Paketi

## Putanja Klase

## Dokumentacioni Komentari

## Hintovi za Dizajniranje Klasa

# Nasledjivanje

# Interfejs, Lambda Izrazi, i Unutrasnje Klase


