---
title: Naučno izračunavanje --- Belekške
author: Andrija Urošević
output: pdf_document
---

# Rešavanje problema matematičkim metodama

- **Modelovanje**
  - Relevantne veličine, njihovo kvantitativno izražavanje i odnos između njih: *matematički model* $M$.
  - Pitanje na koje želimo dobiti odgovor: *matematički problem* $P$.
- **Rešavanje**
  - Primena metode koja može rešiti problem $P$.
  - Dobijamo rešenje $S$.
- **Interpretacija**
  - Rešenje $S$ u modelu $M$, interpretirano u terminima polaznog problema.

## Modelovanje problema

- Poteškoće pri modelovanju
  - Potrebno je procizno uočiti relevantne vrednosti i odnose između njih, treba opisati odgovarajućim formalnim matematičkim jezikom.
  - Kako modelujemo problem direktno utiče na to koji metod rešavanja možemo da primenimo.
- Matematički model
  - Apstrakcija polaznog problema, kako se fokusiramo samo na relevantna svojstva problema.
  - Skup promenljivih predstavlja relevantne vrednosti.
  - Skup formula predstavlja relevantne odnose između tih vrednosti.
- Formulacija
  - Matematička teorija koja ima pogodna svojstva (diferencijabilnost, konveksnost,...) se preporučuje pri formulisanju modela. Razlog tome je šira primena metoda za rešavanje tog problema.
- Pojednostavljenje modela
  - Model uprostimo sve dok je greška rešenja prihvatljiva.
  - Neke tehnike:
    - Zamena beskonačkih procesa konačnim
    - Zamena opštih matrica specifičnim matricama: blok dijagonalne, dijagonalne, trougaone,...
    - Zamena proizvoljnih funkcija jednostavnijim funkcijama: polinimima, konveksnim funkcijama....
    - Zamena nelinearnih problema linearnim problemima.
    - Zamena diferencijalnih jednačina algebarskim jednačinam.
    - Zamena beskonačno dimenzionih prostora konačno dimenzionim prostorima.
  - Da bi tehnike pojednostavljenja bile relevantne potrebno je da:
    - alternativni problem možemo lakše rešiti, a čije rešenje nije drastično drugačije od polaznog;
    - transformacija tekućeg problema u lakši problme dozvoljava izračunavanje rešenja tekućeg problema pomoću rešenja lakšeg problema.
- Upozorenja:
  - Model ne oslikava precizno stvarnost
  - Model može biti dobar u nekim aspektima, a loš u drugim.
  - Podešavanje podataka dovodi do prilagođavanju modelu, u praksi ne daje dobre rezultate.
  - Ne treba se držati modela koji ne rade.

## Rešavanje problema

- Obično sam metod rešavanja dolazi na osnovu dobro izabranog modela problema.
- U nekim slučajevima sam model nema metodu koja može da se primeni.

## Interpretacija rešenja

- Kada dobijemo rešenje modela, primenjujemo inverzne transofrmacije pojednostavljivanja nad tim rešenjem.
- Transformisano rešenje razmatramo u terminima veza stvarnih fenomena i promenljivih u modelu.
  - Treba voditi računa o jedinicama.

## Aproksimacija i greške u izračunavanju

- Greške pre samog naučnog izračunavanja:
  - **Modelovanje**: Apstrakcija i pojednostavljenje dovode do greške
  - **Empirijska merenja**: Uključuju dozu neprekidnosti zbog nesavršenosti mernih instrumenata
  - **Prethodna izračunavanja**: Ulazni podaci mogu biti rezultat nekog prethodnog izračunavanja, pa se greška tako akumulira.
- Prethodni problemi nisu otkljivi, sledeća dva jesu:
  - **Diskretizacija i odsecanje**: Povećanjem granularnosti smanjujemo grešku. Beskonačne procese koje zamenjujemo konačnim možemo kontrolisati njihov broj koraka.
  - Zaokruživanje: Broj decimala koje se koriste za zapis realnih brojeva.
- Dve grupe grešaka: (1) *Greške podataka*; (2) *Greške izračunavanja*.
- **Procena greške**. Za pravu i približnu vrednost $x$ i $x'$ definišemo greške:
  - *Apsolutna greška*: $E(x, x') = |x - x'|$.
  - *Relativna greška*: $R(x, x') = \frac{|x - x'|}{|x|}$

## Stabilnost, uslovljenost i regularizacija

- Algoritam je *nestabilan* ukoliko se njegova greška akumilira tokom njegovog izvršavanja, u suprotom algoritam je *stabilan*.
- *Poništavanje* je slučaj kada je relativna greška mala usled oduzimanja realnih vrednosti koje nose grešku.
- Problem je *loše uslovljen* ako za malo različite podatke na ulozu daje drastično različita rešenja.
- Neka su $\alpha$ ulazi podaci, i $x(\alpha)$ rešenja problema $P$. Tada *uslovljenost* problem $P$ definišemo kao 
$$Cond(P) = \frac{R(x(\alpha), x(\alpha'))}{R(\alpha, \alpha')} = \frac{|x(\alpha) - x(\alpha')|/|x(\alpha)|}{|\alpha - \alpha'|/|\alpha|}.$$
  - Uslovljenost funkcije $f$: 
  $$Cond(f) = \frac{|f(x) - f(x + \Delta x)|/|f(x)|}{|\Delta x|/|x|} \approx |x f'(x) / f(x)|$$
  - Uslovljenost matrice $A$: 
  $$Cond(A) = |A^{-1}||A|$$
  - Uslovljenost sistema $Ax = b$: 
  $$
  \begin{aligned}
  Cond(P) &= \frac{|A^{-1}b - A^{-1}(b + \Delta b)|/|A^{-1}b|}{|\Delta b|/|b|} \\
          &= \frac{|A^{-1} \Delta b|/|A^{-1}b|}{|\Delta b|/|b|} \\
          &= \frac{|A^{-1} \Delta b|}{|\Delta b|} \frac{|Ax|}{|x|}
  \end{aligned}
  $$.    
- Lošu uslovljenost rešavamo *regularizacijom*.
  - Zamenjujemo problem koji je loše uslovljen bliskim problemom koji je dobro uslovljen.
  - Razlika između ta dva problema treba da bude podesiva nekim parametrom, tj. kada parametar teži nuli problemi su jednaki.

# Aproksimacija funkcija

- Aproksimacija funkcije $f$ je funkcija $g$ koja je funkciji $f$ bliska u nekom unapred definisanom smislu.
- Aproksimacija funkcija se vrši iz različitih razloga:
  - pojednostavljanje evaluacije funkcije;
  - zamenom funkcije nekom funkcijom sa boljim matematičkim osobinama;
  - ne znamo simboličku reprezentaciju funkcije već samo njene vrednosti u nekim tačkama.
- Postoje razni kriterijumi za aproksimaciju:
  - $\|f - g\|_2^2 = \int_a^b (f(x) - g(x)) ^ 2 dx;$ (kriterijum je površina izmedju dve funkcije)
  - $\|f - g\|_2^2 = \sum_{i=1}^n (f(x_i) - g(x_i)) ^ 2;$ (ukupno odstupanje u svim tačkama u kojima je vrednost funkcije poznata)
  - $\|f - g\|_{\infty} = \sup_{x \in [a, b]} |f(x) - g(x)|.$ (samo najveće odstupanje je bitno)

## Primeri problema aproksimacije funkcija

- Problem linearne aproksimacije:
    - Aproksimacija: $g(x, \alpha) = \alpha_0 + \sum_{i=1}^n \alpha_i x_i.$
    - Kriterijum: $\min_\alpha \sum_{i=1}^N(g(x_i, \alpha) - f(x_i))^2.$
- Problem rekonstrukcije zamućene slike operatorom $A$:
    - $x = A^{-1} y$ ne daje dobro rešenje, kako je $A$ loše uslovljena matrica.
    - Regularizacija obezbeđuje da se susedni pokseli ne razlikuju mnogo:
$$ \min_x \|Ax - y\|^2 + \lambda(\sum_{i=1}^M \sum_{j=1}^{N-1}(x_{i,j} - x_{i,j+1})^2 + \sum_{i=1}^{M-1}\sum_{j=1}^N(x_{i,j} - x_{i+1,j})^2) $$
- Problem konstrukcije slike od $N$ slika različitih delova iste scene.
  - Moramo uračunati razlike među delovima slika: To su rotacija kamere za ugao $\theta$, translacija kamere za vektor $(u, v)$ i skaliranje za vrednost $s$. Jedna takva veza može biti data matricom transformacije ($a = s \cos \theta, b = s \sin \theta$ i $s = \sqrt{a^2 + b^2}$):
  $$G=\begin{pmatrix} a & -b & u \\ b & a & v \\ 0 & 0 & 1\end{pmatrix},$$
  - Potrebno je još odrediti i upariti detalje na slikama (postoji algoritam). Neka je skup lokacija detalja $\{x_{ij} | j = 1,\ldots,M\}$, i za svake dve slike $i$ i $j$ dat $F(i, j)$ skup indeksa detalja koji su uspešno upareni.
  - Konačan optimizacioni problem postaje ($G_i$ matrica transformacije sa parametrima $(a_i, b_i, u_i, v_i)$):
  $$\min_{\mathbf{a}, \mathbf{b}, \mathbf{u}, \mathbf{v}} \sum_{i=1}^N \sum_{j=i+1}^N \sum_{k \in F(i, j)} \|G_i x_{ik} - G_j x_{jk}\|^2$$.
- Određivanje koordinata GPS uređaja:
  - $(u, v, w)$ koordinate GPS uređaja koje treba izračunati;
  - $(p_i, q_i, r_i)$ koordinate $i$-tog satelita;
  - $\rho_i$ udaljenost $i$-tog satelita od GPS uređaja.
  - Za svaki satelit treba da važi: $\sqrt{(u - p_i)^2 + (v - q_i)^2 + (w - r_i)^2} = \rho_i$.
  - Problem se svodi na:
  $$\min_{u,v,w} \sum_{i=1}^n (\sqrt{(u - p_i)^2 + (v - q_i)^2 + (w - r_i)^2} - \rho_i)^2.$$
 
## Aproksimacija u Hilbertovim prostorima

- Vektorski prstor koji je kompletan u odnosu na metriku indukovanu skalarnim proizvodom $d(x,y)=\|x-y\| = \sqrt{(x-y)\cdot(x-y)}$ se naziva *Hilbertovim prostorom*.
  - $\mathbb{R}^n$ je Hilbertov prostor
  - $\mathcal{L}_2[a, b]$ prostor funkcija koje su integrabile sa kvadratom na intervalu $[a, b]$ je Hilbertov prostor. 
- Sistem vektor $\{ e_i | i \in \mathbb{N}\}$ je *ortonormiran* ako
$$e_i \cdot e_j = \begin{cases}1 & i = j \\ 0 & i \neq j \end{cases} \quad i, j \in \mathbb{N}.$$
- Neka je $\{ e_i | i \in \mathbb{N}\}$ ortonormiran sistem vektora Hilbertovog prostora $\mathcal{H}$. Koeficijenti $x \cdot e_i$ nazivaju se *Furijeovi koeficijenti* vektora $x \in \mathcal{H}$, a red $\sum_{i=1}^\infty (x \cdot e_i) e_i$ se naziva *Furijevo red* vektora $x \in \mathcal{H}$.

**Teorema 1** Za ortonormirani sistem $\{ e_i | i \in \mathbb{N}\}$ u Hilbertovom prostoru $\mathcal{H}$, sledeća tvrđenja su ekvivalentna:

- Za svako $x \in \mathcal{H}$ i svako $\varepsilon > 0$, postoje skalari $\lambda_1,\lambda_2,\ldots,\lambda_n$, takvi da važi $\|x - \sum_{i=1}^n \lambda_i e_i\| < \varepsilon$.
- Za svako $x \in \mathcal{H}$ važi $\sum_{i=1}^\infty (x \cdot e_i) e_i = x$ (pri čemu se podrazumeva konvergencija u smislu metrike prostora $\mathcal{H}$)
- Za svako $x \in \mathcal{H}$ važi $\sum_{i=1}^\infty (x \cdot e_i)^2 = \|x\|^2$ (Parselova jednakost)
- Ako je vektor $x \in \mathcal{H}$ takav da je $x \cdot e_i = 0$ za svako $i \in \mathbb{N}$, onda važi $x = 0$.

**Teorema 2** Neka je $f$ element Hilbertovog postora $\mathcal{H}$ i neka je $\mathcal{H}'$ njegov potprostor čiju bazu čine elementi $\{g_1, g_2, \ldots, g_n\}$. Postoji element najbolje aproksimacije $g^* = \sum_{i=1}^n c_i^* g_i \in \mathcal{H}'$, takav da važi

$$\left\|f - \sum_{i=1}^n c_i^* g_i\right\| = \inf_{c_1,\ldots,c_n} \left\|f - \sum_{i=1}^n c_i g_i\right\|.$$

Dodatno, važi da je $(f - g^*) \cdot x = 0$ za sve $x \in \mathcal{H}'$ akko je $g^*$ element najbolje aproksimacije za $f$ iz $\mathcal{H}'$.

- Element najbolje aproksimacije za $f$ je njegova ortogonalna projekcija na prostor $\mathcal{H}'$!!!
- Keoficijenti najblje aproskimacije se mogu odrediti iz sistema:
$$\sum_{i=1}^n c_i (g_i \cdot g_j) = f \cdot g_j, \quad j=1,\ldots,n$$
- Ako je baza $\{g1,\ldots,g_n\}$ ortogonalna, svi skalarni proizvodi $g_i \cdot g_j$ su jednaki nuli ako $i \neq j$, tako da u tom slučaju nije potrebno rešavati sistem jednačina već je dovoljno izračunati skalarne proizvode i izraziti koeficijente $c_i$ iz dobijenih jednakosti u kojima učestvoje po jedan keoficijent $c_i$.

## Srednjekvadratna aproksimacija

- Neka je $\mathcal{L}_2[a,b]$ Hilbertov prostor funkcija integrabilnih sa kvaratom na intervalu $[a, b]$, u kome je norma definisana integralom $\|f\|^2 = \int_a^b f^2(x) dx$ onda se element najbolje aproksimacije naziva elementom *najbolje srednjekvadratne aproksimacije*.
- Ako je funkcija $f$ definisana na konačnom skupu tačaka $\{x_0,\ldots,x_m\}$ integral zamenjujemo sumom, tj. $\|f\|^2 = \sum_{i=1}^m f^2(x_i)$. 
- Metoda koja rešava srednjekvadratnu aproksimaciju na konačnom skupu tačaka naziva se *metoda najmanjih kvadrata* (engl. *least squares method*).
- Sistem koji se rešava uzima sledeći oblik:
$$\sum_{i=1}^n c_i \sum_{k=1}^m g_i(x_k) g_j(x_k) = \sum_{k=1}^m f(x_k)g_j(x_k) \quad j=1,\ldots,n.$$
$$\sum_{k=1}^m g_j(x_k) \left( \sum_{i=1}^n c_i g_i(x_k) \right) = \sum_{k=1}^m f(x_k)g_j(x_k) \quad j=1,\ldots,n.$$
$$A^T A x = A^T b$$
$$x = (A^T A)^{-1} A^T b$$
- Prethodna jednačina predstavlja rešenje problema
$$\min_x \|Ax - b\|^2.$$
- Drugi način izvođenja rešenja:
$$\begin{aligned}
\|Ax - b\|^2 &= (Ax - b)^T (Ax - b) \\ 
             &= ((Ax)^T - b^T) (Ax - b) \\
             &= (x^T A^T - b^T) (Ax - b) \\
             &= b^T b - x^T A^T b - (b^T A x)^{T^T} + x^T A^T A x \\
             &= b^T b - x^T A^T b - (x^T A^T b)^T + x^T A^T A x \\
             &= b^T b - 2 x^T A^T b + x^T A^T A x
\end{aligned}$$
- Izjednačavanjem gradijenta po $x$ sa nulom dobijamo:
$$2 A^T A x - 2 A^T b = 0.$$
- Matrica $(A^T A)^{-1} A^T$ je *Mur-Penrouzov pseudoinverz* matrice $A$.
- Metod srednjekvadratne aproksimacije se često koristi za rešavanje problema linearne regresije.

**Teorema 3 (Gaus-Markov)** Ukoliko važi $E(\varepsilon) = 0$ i $cov(\varepsilon) = \sigma^2$, za konstantno $\sigma^2 > 0$, onda za ocenu $\hat{w} = (X^T X)^{-1} X^T y$ važi
$$E(\hat{w}) = w, cov(\hat{w}) = \sigma^2 (X^T X)^{-1}.$$
Takođe, za svaku nepristrasnu linearnu ocenu $\tilde{w}$ parametra $w$ važi
$$\sum_{i=1}^n(w_i - \hat{w}_i)^2 \leq \sum_{i=1}^n (w_i - \tilde{w}_i)$$

- Ukoliko je matrica $A^T A$ loše uslovljena (kolone ili vrste matrice $A$ su visoko korelisane), tada se koristi regularizacija i rešava se problem (*Tihonovljeva regularizacija* ili *grebena regularizacija*):
$$\min_x \|Ax - b\|^2 + \lambda \|x\|^2$$
- Slično kao u prethodnom slučaju:
$$\|Ax - b\|^2 + \lambda \|x\|^2 = (Ax - b)^T(Ax - b) + \lambda x^T x = b^T b - 2 x^T A^T b + x^T A^T A x + \lambda x^T x.$$
- Računanjem gradijenta po $x$ i izjednačavanjem sa nulom dobijamo:
$$A^T Ax - A^T b + \lambda x = 0$$
$$x = (A^T A + \lambda I)^{-1} A^T b$$
- Uklanjanje šuma iz signala:
$$\min_x \|x - y\|^2 + \lambda \sum_{i=1}^{n-1} (x_i - x_{i+1})^2$$
  - Uvodimo matricu $D$:
  $$
  \begin{pmatrix} 
  1 & -1 &  0 & \ldots & 0 & 0 & 0 \\
  0 &  1 & -1 & \ldots & 0 & 0 & 0 \\
  \vdots & \vdots & \vdots & \ddots & \vdots & \vdots & \vdots \\
  0 &  0 &  0 & \ldots & 1 & -1 & 0 \\
  0 &  0 &  0 & \ldots & 0 & 1 & -1 \\
  \end{pmatrix}
  $$
  - Dati problem postaje:
  $$\min_x \|Ix - y\|^2 + \|\sqrt{\lambda} Dx - 0\|^2$$
  $$\min_x \left\| \begin{pmatrix}I \\ \sqrt{\lambda} D\end{pmatrix} x - \begin{pmatrix} y \\ 0 \end{pmatrix}\right\|^2$$
  - Odgovarajuce rešenje:
    $$x = (I + \lambda D^T D)^{-1} y$$
- Rekonstrukcija zamućene slike:
$$ \min_x \|Ax - y\|^2 + \lambda(\sum_{i=1}^M \sum_{j=1}^{N-1}(x_{i,j} - x_{i,j+1})^2 + \sum_{i=1}^{M-1}\sum_{j=1}^N(x_{i,j} - x_{i+1,j})^2) $$
  - Uvodimo matricu $D_h$ i $D_v$:
    $$
    \begin{pmatrix}
    I & -I &  0 & \ldots & 0 & 0 & 0 \\
    0 &  I & -I & \ldots & 0 & 0 & 0 \\
    \vdots & \vdots & \vdots & \ddots & \vdots & \vdots & \vdots \\
    0 &  0 &  0 & \ldots & I & -I & 0 \\
    0 &  0 &  0 & \ldots & 0 & I & -I \\
    \end{pmatrix}
    \quad
    \begin{pmatrix}
    D & 0 & \ldots & 0 \\
    0 & D & \ldots & 0 \\
    \vdots & \vdots & \ddots & \vdots \\
    0 & 0 & \ldots & D \\
    \end{pmatrix}
    $$
  - Problem možemo zapisati kao:
    $$\min_x \|Ax - y\|^2 + \|\sqrt{\lambda} D_v x - 0\|^2 + \|\sqrt{\lambda} D_h x - 0\|^2$$
    $$\min_x \left\| \begin{pmatrix} A \\ \sqrt{\lambda} D_v \\ \sqrt{\lambda} D_h \end{pmatrix} x - \begin{pmatrix} y \\ 0 \\ 0 \end{pmatrix}\right\|^2$$
  - Odgovarajuće rešenje:
    $$x = (A^T A + \lambda D_v^T D_v + \lambda D_h^T D_h)^{-1} A^T y$$

## Furijeova transformacija

- Trigonometrijski Furijeov red se zasniva na sistemu različitih frekvencija $\cos(kx)$ i $\sin(kx)$ za $k=0,1,\ldots$.
- Furijeovi koeficijenti omogućavaju analizu signala u odnosu na frekvencije koje su u njemu zastupljene, odnosno *spektar signala*. ???
- *Furijeova transformacije* prevodi reprezentaciju funkcije iz vremenskog domena u frekvencijski domen.
  - *Inverzna Furijeova transformacija* radi obrnuto.
  - Neke vrste Furijeovih transformacija: *razvoj u Furijeov red, neprekidna Furijeova transformacija* i *diskretna Furijeova transformacija*.
- Neka je funkcija $f$ periodnična i integrabilna na intervalu $[a, b]$. Tada se može razviti u Furijeov red:
$$f(t) = \frac{a_0}{2} + \sum_{k=1}^\infty\left(a_k \cos \left( \frac{2 \pi k t}{b - a}\right) + b_k \sin \left(\frac{2 \pi k t}{b - a}\right)\right),$$
$$a_k = \frac{2}{b - a} \int_a^b f(t) \cos \left(\frac{2 \pi k t}{b - a}\right) dt, \quad k=0,1,2,\ldots$$
$$b_k = \frac{2}{b - a} \int_a^b f(t) \sin \left(\frac{2 \pi k t}{b - a}\right) dt, \quad k=1,2,3,\ldots$$

- *Primer*: $f(t) = 5\cos(2t) + 3\sin(8t)$ je periodična na intervalu $[0, \pi]$. Odatle svi Furijeovim koeficijenti su 0 sem $a_1 = 5$ i $b_4 = 3$.
- Komleksna reprezentacije Furijeovog reda:
$$f(t) = \sum_{k=-\infty}^\infty \hat{f}_k e^{\frac{-2 \pi i k t}{b - a}}$$
$$\hat{f}_k = \frac{1}{b-a} \int_a^b f(t) e^{\frac{2 \pi i k t}{b - a}} dt$$
- Odnos između realne i kompleksne reprezentacije su u tesnoj vezi:
$$a_0 = 2 \hat{f}_0$$
$$a_k = \hat{f}_k + \hat{f}_{-k}$$
$$b_k = i \hat{f}_{-k} - \hat{f}_k$$
- Za koeficijente važi $\overline{\hat{f}_k} = \hat{f}_{-k}$:
$$\begin{aligned}
\overline{\hat{f}_k} &= \overline{\frac{1}{b-a} \int_a^b f(t) e^{\frac{2 \pi i k t}{b - a}} dt}\\
                     &= \frac{1}{b-a} \int_a^b \overline{f(t) e^{\frac{2 \pi i k t}{b - a}}} dt\\
                     &= \frac{1}{b-a} \int_a^b f(t) e^{\frac{-2 \pi i k t}{b - a}} dt\\
                     &= \hat{f}_k
\end{aligned}$$
- Promenljiva $t$ predstavlja vreme, dok Furijeovi koeficijenti $\hat{f}_k$ predstavljaju intenzitet odgovarajućih frekvencija u signalu. 
  - U razvoju u Furijeov red vremenski domen je neprekidno, ali je frekvencijski domen diskretan, tj. periodična funkcija se može predstaviti preko beskonačno mnogo broja sinusa i kosinusa, ali sa diskretnim frekvencijama. 
  - Ovaj problem se prevazilazi prelaskom sa reda na intergral (Furijeova transformacija i inverzna Furijeova transformacija):
$$\hat{f}(u) = \int_{-\infty}^{+\infty} f(t) e^{2 \pi i u t} dt$$
$$f(t) = \int_{-\infty}^{+\infty} \hat{f}(u) e^{-2 \pi i u t} du$$
  - Mana ovih metoda je što je funkcija $f$ obično poznata samo na konačnom skupu tačaka.
  - Neka su vrednosti funkcije $f_j = f(t_j)$, gde je $t_j = t_0 + jh$, za $j=0,1,\ldots,n-1$ i $h>0$. Tada:
$$\hat{f}_k = \frac{1}{n}\sum_{j=0}^{n-1} f_j e^{\frac{k2 \pi i  j}{n}} \quad k=0,1,\ldots,n-1$$
$$f_k = \frac{1}{n}\sum_{k=0}^{n-1} \hat{f}_k e^{-\frac{2 \pi i k j}{n}} \quad j=0,1,\ldots,n-1$$
- *Primer* uklanjanje šuma: Signal $-$(FFT)$\rightarrow$ Frekvencije $-$(clamp)$\rightarrow$ Frekvencije (bez viskokih) $-$(IFFT)$\rightarrow$ Signal (bez šuma).
- Furijeova transformacija u dve dimenzije:
  - Nekprekidna:
  $$\hat{f}(u,v) = \int_{-\infty}^{+\infty} \int_{-\infty}^{+\infty} f(x,y) e^{2 \pi i (xu + yv)} dx dy$$
  $$f(x,y) = \int_{-\infty}^{+\infty} \int_{-\infty}^{+\infty} \hat{f}(u,v) e^{- 2 \pi i (xu + yv)} du dv$$
  - Diskretna:
  $$\hat{f}_{lm} = \frac{1}{PQ} \sum_{j=0}^{P-1} \sum_{k=0}^{Q-1} f_{jk} e^{2 \pi i \left(\frac{jl}{P} + \frac{km}{Q}\right)}$$
  $$f_{jk} = \sum_{l=0}^{P-1} \sum_{m=0}^{Q-1} \hat{f}_{lm} e^{-2 \pi i \left(\frac{jl}{P} + \frac{km}{Q}\right)}$$
- Koeficijenti Furijeove transformacije su, kao kompleksni brojevi, određeni modulom ili *amplitudom* i argumentom ili *fazom*.
  - Amplituda predstavlja jačinu nekog signala.
  - Faza predstavlja pomeraj frekvencije duž vremenske ose.
- *Dirakova delta funkcija* i $f(x,y)=\delta(x,y)=\delta(x)\delta(y)$
- *Odsecanje dela spektra*:
    - Odsecanje viših frekvencija omogućava grub prikaz slike (uklanja ivice)
    - Odsecanje nižih frekvencija omogućava prepoznavanje ivica (istače ivice)
    - Uklanjanjem prepoznatljivih maksimuma uklanjaju se poreiodične strukture na slici.

### Brza Furijeova transformacija

- DFT (Diskretna Furijeova transformacija) ima složenost $\Theta(n^2)$.
- FFT (Brza Furijeova transformacija) ima složenost $\Theta(n\log n)$.
- Uvodimo $n$-ti koren jedinice $w = e^{\frac{2 \pi i}{n}}$, 
  - Važi $w^n=1$:
    $$w^n = e^{\frac{2 \pi i}{n}n} = e^{2 \pi i} = 1$$
  - Važi $w^{k + \frac{n}{2}} = - w^k$:
    $$w^{k + \frac{n}{2}} = e^{\frac{2 \pi i}{n}(k + \frac{n}{2})} = e^{\frac{2 \pi i k}{n} + \pi i} = e^{\pi i} e^{\frac{2\pi i k}{n}} = - w^k$$
- Diskretna Furijeovra transformacija postaje:
  $$\hat{f}_k = \frac{1}{n}\sum_{j=0}^{n-1}f_j w^{kj} \quad k=0,1,2,\ldots,n-1$$
  - Važi $\hat{f}_{k + n} = \hat{f}_k$:
  $$\hat{f}_{k + n} = \frac{1}{n}\sum_{j=0}^{n-1}f_j w^{(k+n)j} = \frac{1}{n}\sum_{j=0}^{n-1}f_j w^{kj} = \hat{f}_k$$
  - Keoficijenti se mogu izračunati preko parnih i neparnih elementa:
  $$\hat{f}_k = \frac{1}{n}\sum_{j=0}^{n-1}f_j w^{kj} = \frac{1}{n}\sum_{j=0}^{n/2-1}f_{2j} w^{2jk} + \frac{1}{n}\sum_{j=0}^{n/2-1}f_{2j+1} w^{(2j+1)k} = $$ 
  $$ = \frac{1}{2}\frac{1}{n/2}\sum_{j=0}^{n/2-1}f_{2j} w^{2jk} + \frac{1}{2}w^k\frac{1}{n/2}\sum_{j=0}^{n/2-1}f_{2j+1} w^{(2j+1)k} = \frac{1}{2}(E_k + w^k O_k)$$
  - Takođe, važi:
  $$E_{k + n/2} = E_k$$
  $$O_{k + n/2} = O_k$$
  - Dobijamo:
  $$\hat{f}_k = \begin{cases}\frac{1}{2}(E_k + w^k O_k) & 0 \leq k < \frac{n}{2} \\ \frac{1}{2}(E_{k - \frac{n}{2}} + w^k O_{k - \frac{n}{2}}) & \frac{n}{2} \leq k < n\end{cases}$$
  - Konačno:
  $$\hat{f}_k = \frac{1}{2}(E_k + w^k O_k)$$
  $$\hat{f}_{k + \frac{n}{2}} = \frac{1}{2}(E_k - w^k O_k)$$
- Algoritam FFT se može koristiti i kao algoritam za inverzni FFT, tako što se pre primene algoritma FFT, ulaz konjuguje, a nakon primene algoritma FFT, izlaz konjuguje.

### Konvolucija

- Da li postoji neka aritmetička veza između operacija nad signalima i nekih operacija nad njihovim Furijeovim transformacijama?
  - Važi:
  $$\begin{aligned}
  \widehat{f + g}(u) &= \int_{-\infty}^{+\infty} (f + g)(t) e^{2 \pi i u t} dt \\
                 &= \int_{-\infty}^{+\infty} (f(t) + g(t)) e^{2 \pi i u t} dt \\
                 &= \int_{-\infty}^{+\infty} f(t) e^{2 \pi i u t} dt + \int_{-\infty}^{+\infty} f(t) e^{2 \pi i u t} dt \\
                 &= \hat{f}(u) + \hat{g}(u)
  \end{aligned}$$
  - Takođe, 
  $$\begin{aligned}
  \hat{f}(u)\hat{g}(u) &= \int_{-\infty}^{+\infty} f(x) e^{2 \pi i u x} dx \int_{-\infty}^{+\infty} g(y) e^{2 \pi i u y} dy \\
                       &= \int_{-\infty}^{+\infty} \int_{-\infty}^{+\infty} f(x) g(y) e^{2 \pi i (x+y) u} dx dy \\
                       &= \int_{-\infty}^{+\infty} \int_{-\infty}^{+\infty} f(x) g(v - x) e^{2 \pi i v u} dx dv \\
                       &= \int_{-\infty}^{+\infty} (\int_{-\infty}^{+\infty} f(x) g(v - x) dx) e^{2 \pi i v u} dv \\
                       &= \int_{-\infty}^{+\infty} (f * g)(v) e^{2 \pi i v u} dv 
  \end{aligned}$$
  $$(f*g)(v) = \int_{-\infty}^{+\infty} f(x) g(v - x) dx$$
  - Operacija $*$ se naziva operacijom *konvolucije*.

**Teorema 5 (o konvoluciji)**:
    $$\widehat{f * g} = \hat{f}\hat{g}$$
    $$\widehat{f g} = \hat{f} * \hat{g}$$
    $$f * g = g * f$$
    $$(f * g) * h = f * (g * h)$$
    $$f * (g + h) = f * g + f * h$$
    $$f * \delta = f$$

- Konvolucija u diskretnom smislu:
$$(f*g)_i = \sum_{j=0}^{n-1}f_j g_{i-j} \quad i=0,1,\ldots,n-1$$
- Konvolucija u dve dimenzije:
$$(f*g)(u,v) = \int_{-\infty}^{+\infty} f(x,y)g(u-x, v-y) dx dy$$
$$(f*g)_{i,j} = \sum_{k=0}^{m-1} \sum_{l=0}^{n-1} f_{k,l} g_{i-k,j-l}$$
- Po definiciji konvolucija dva signala ima vremensku složenost $\Theta(n^2)$. Ali primenom FFT algoritma, konvoluciju možemo izračunati u $\Theta(n \log n)$ (zbog teoreme o konvoluciji $(\widehat{f*g}) = \hat{f}\hat{g}$).
  - $f$ i $g$ $-$(FFT)$\rightarrow$ $\hat{f}$ i $\hat{g}$ $-$(množenje)$\rightarrow$ $\hat{f}\hat{g}$ $-$(teorema o konvoluciji)$\rightarrow$ $\widehat{f*g}$ $-$(IFFT)$\rightarrow$ $f*g$
- *Primer*: Množenje polinoma je konvolucija
$$f(x) = \sum_{i=1}^m f_i x^i \quad g(x)=\sum_{i=1}^n g_i x^i$$
  - Proizvod je veličine $m + n + 1$, te ulazne podatke proširujemo $(f_1, f_2, \ldots, f_m, 0,\ldots,0)$ i $(g_1, g_2, \ldots, g_n, 0,\ldots,0)$.
  - Množenje polinoma ima složenost $\Theta((n + m)\log (n + m))$.
- Konvolucija se koristi tako što je jedna funkcija signal, a druga funkcija predstavlja neku jednostavnu funkciju kojom transformišemo signal. Tu funkciju zovemo *filter*.
- Filter Gausovog zamućivanja.
  - Gausovo zvono: $\frac{1}{2 \pi \sigma^2} e^{- \frac{x^2 + y^2}{2 \sigma^2}}$
  - Uprošćeni filter zamućivanja:
  $$\frac{1}{9}\begin{pmatrix}1 & 1 & 1 \\ 1 & 1 & 1 \\ 1 & 1 & 1\end{pmatrix}$$
- Filteri za otkrivanje ivica:
  - Sobel-Feildmonove vertikalne i horizontalne ivice:
  $$G_x = \begin{pmatrix}1 & 0 & -1 \\ 2 & 0 & -2 \\ 1 & 0 & -1 \end{pmatrix} * A \quad G_y = \begin{pmatrix}1 & 2 & 1 \\ 0 & 0 & 0 \\ -1 & -2 & -1 \end{pmatrix} * A $$
  - Aproksimacija intenziteta gradijenta je onda
  $G = \sqrt{G_x^2 + G_y^2}$
- Brzo pronalaženje uzorka slike $g$ u drugoj slici $f$.

## Osnovni koncept obrade signala

### Uzorkovanje

### Curenje spektra

### Filtriranje signala

## Talasići

# Numerička linearna algebra

## Primeri problema numeričke linearne algebre

## Dekompozicija matrica

## Sopstveni vektori matrica

## Retki sistemi linearnih jednačina

## Inkrementalni pristup rešavaju problema linearne algebre

# Matematička optimizacija

## Primeri praktičnih problema neprekidne matematičke optimizacije

## Neprekidna optimizacija

## Diskretna optimizacija
