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
    ```
    int vacationDays;
    vacationDays = 12;
    ```
  * Deklaracija i inicijalizacija:
    ```
    int vacationDays = 12;
    ```
* Deklaracija ili inicijalizacija se mogu naci bilo gde u kodu.

### Konstante

* U javi se koristi kljucna rec `final` da konstante.
```
final double CM_PER_INCH = 2.54;
```
* *Klasne konstante* imaju dodato `static` i nalaze se u klasi izvan
  svih funcija kako bi se mogle referisati u svakoj funkciji:
```
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
```
double x = 4;
dobule y = Math.sqrt(x);
double z = Math.pow(x, 4);
```
* Trigonometrijske funkcija:
```
Math.sin
Math.cos
Math.tan
Math.atan
Math.atan2
```
* Eksponencijalne i logaritamske funkcije:
```
Math.exp
Math.log
Math.log10
```
* Konstante
```
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
```
double x = 9.997;
int nx = (int) x; // nx = 9
int mx = (int) Math.round(x); // nx = 10 Math.round(x) vraca long 
                              // te je potrebno kastovanje
```

### Kombinovanje Dodele sa Operatorima
```
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
```
enum Size { SMALL, MEDIUM, LARGE, EXTRA_LARGE };
Size s = Size.MEDIUM;
```

## String

* Java `String` je sekvenca Unicode karaktera.
* Ne postoji predefinisani `String` tip, vec je on u formi klase.
* Svaki navedeni string je instanca klase `String`.
```
String e = "";
String greeting = "Hello";
```

### Podstring

```
String greeting = "Hello";
String s = greeting.substring(0, 3); // s = "Hel"
```

### Konkatinacija ili Nadovezivanje

```
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
```
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

```
Scanner in = new Scanner(System.in);
String name = in.nextLine();  // cita celu liniju (string)
String firstName = in.next(); // cita sledecu rec (string)
int age = in.nextInt();       // cita sledeci int
int hight = in.nextDouble();  // cita sledeci double
in.close();         
```

### Formatiranje Izlaza

```
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
```
Scanner in = new Scanner(Paths.get("myfile.txt"), "UTF-8");
```
* Za pisanje u fajl:
```
PrintWriter out = new PrintWriter("myfile.txt", "UTF-8");
```
* Kod citanja iz fajlova ako fajl ne postoji na toj putanji dolazi
  do *exception*. Java koristi drugacije nacine za obradjivanje expections. 

## Controla Toka

### Blokovi

* Blokovi sadrze nekoliko Java naredbi, koje objedinjuju par 
  viticastih zagrada `{ }`.
* Blokovi se mogu ugnjezditi u druge blokove.
```
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

```
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

```
while (condition) statement

do statement while (condition);
```

### Determinisane Petlje

```
for (initStatement; condition; ithStatement)
    statement
```

### Switch naredba

```
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
```
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
```
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

```
for (variable : collection) statement
```
* `collection` izraz mora da bude niz ili objekat koji implementira
  `Iterable` interfejs, kao sto je na primer `ArrayList`.
```
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

```
int[] smallPrimes = { 2, 3, 5, 7, 11, 13 }; 
new int[] {17, 19, 23, 29, 31, 37} // Anonimni niz
```
* Anonimni nizovi se mogu koristiti kod ponovne inicijalizacije nekog niza
  kako se ne bi kreirao novi niz.
```
smallPrimes = new int[] {17, 19, 23, 29, 31, 37}; 
// je krace od
int[] tmp = {17, 19, 23, 29, 31, 37};
smallPrimes = tmp;
```

### Kopiranje Nizova

* Moguce je kopiranje jedne promenljive niza u drugu, ali onda obe
  promenljive referisu na isti niz:
```
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
```
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

```
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
  * ```
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
```
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
    
# Objekti i Klas

# Nasledjivanje

# Interfejs, Lambda Izrazi, i Unutrasnje Klase


