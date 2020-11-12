# OpenGL

* OpenGL je definisan kao **automat**. API pozivi menjaju OpenGL 
  stanje, postavljaju upit nekom delu stanja, ili ta stanja koriste
  za renderovanje necega.

# OpenGL Objekti

* **OpenGL Objekat** je OpenGL konstrukt koji sadrzi neko stanje.
  * Kada se pobezu za contekst, stanje koje sadrzi se preslikava
    u kontekstovo stanje.
* Objekti su uvek kontejneri za stanja. Svaki objekat je definisan
  sa stanjem koje sadrzi.
  * Enkapsulira neku grupu stanja i menja ih pozivom neke funkcije.
* !Ovako je specifikovana, sto ne mora da znaci da se ovako 
  implementira. Ali dovoljno je znati da ce se ovako ponasati.

## Konstruisanje i Dekonstruisanje Objekta

* Za konstruisanje objekta, generise se njegovo *ime* (int).
  * Ovo stvara referencu na objekat, ali u opstem slucaju ne kreira
    njegova stanja.
```c
void glGen*(GLsizei n, GLuint *objects);
```
* Ova funkcija generise `n` objekta datog tipa, i smesta ih u 
  `objects` niz.
* `GLuint` predstavlja ime objekta, tj. 32-bit unsigned int koji
  jedinstveno identifikuje objekat.
  * 0 je rezervisano za specijalan slucaj.
* Svaki objekat koji vise ne koristimo treba obrisati sa `glDelete*`.
```c
void glDelete*(GLsizei n, const GLuint *objects);
```
* Kada se objekat izbrise, ako je on vezan za trenutni kontekst, onda
  se on odvezuje od njega.
* Pozivanje `glDelete*` na objekat ne garantuje njegovu `trenutnu`
  dekonstrukcuje (njgovog sadrzaja, pa cak i njegovog imena).
  * Taj objekat tada postaje siroce objekat (hehe).
* Objekat *se koristi* ako je:
  1. Vezan za neki kontekst (ne nuzno trenutni).
  2. Ako je spojen za kontejnter objekat.
* Ako se objekat *koristi* onda ce on ostati ziv u OpenGL 
  implementaciji.

## Koriscenje Objekta

* Kako su objekti definisani kao kolekcija stanja, da bi ih 
  modifikovali, moramo ih prvo povezati sa OpenGL kontekstom.
  * Samim tim njihovo stanje se postavlja na trenutno stanje    
    konteksta.
  * Bilo koja funkcija koja menja stanje, upravljena tim objektom,
    ce jednostavno promeniti stanje unutar objekta.
* Povizivanje novo generisanog objekta ce stvoriti novo stanje 
  za taj objekat.
```c
void glBind*(GLenum target, GLuint object);
```
* `target` je gde se drugaciji tipovi objekta razlikuju.
  * buffer objekat se moze povezati sa array buffer, index buffer,
    pixel buffer, transform buffer,...

### Objekat Nula

* `GLuint` vrednost 0 je specijalan objekat, koji se ponasa kao
  null pokazivac: on nije objekat.
* O ovom objektu se moze misliti u smislu *default objekta*.
  * Za teksture on predstavlja ne postojanu teksturu.
  * Za framebuffer on predstavlja *default framebuffer*.

## Visestruko Povezivanje (Multibind)

* Broj tipova objekata moze se povezati na vise targeta. Pa je 
  korisno povezati grupu objekata sa nekim nizom targeta.
  * Ovo se koristi samo za koriscenje stanja objekta, ali ne i za
    zamenu njegovih stanja!
* Za razliku od obicnog vezivanja, ako u funkciji visestrukog 
  vezivanje dodje do greske, ona *moze imati efekat*. 

## Deljenje Objekta

* Moguce je kreirati vise OpenGL konteksta. (zbog toga je svaki od   
  njih thread-specific). Svi oni su skroz odvojeni od drugih, nista
  uradjeno u jednom ne moze uzrokovati drugo.
* Moguce je kreirati kontekst koji deli objekat sa nekim drugim
  vec postojecim kontekstom.
* Promene objekta u jednom kontekstu nece odmah uzrokovati i promene
  u drugom kontekstu kako su oni thead-specific, pa se mora


## Tipovi Objekta

* Regularni objekti
  1. Buffer Objekti
  2. Query Objekti
  3. Renderbuffer Objekti
  4. Sampler Objekti
  5. Texture Objekti
* Konteiner Objekti
  1. Framebuffer Objekti
  2. Program Pipeline Objekti
  3. Transform Feedback Objekti
  4. Vertex Array Objekti
  
