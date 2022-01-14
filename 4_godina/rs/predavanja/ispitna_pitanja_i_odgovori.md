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

