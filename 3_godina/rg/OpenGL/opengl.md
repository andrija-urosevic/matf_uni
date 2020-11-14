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
  
# Vertex Specifikacija

* *Vertex Spesifikacija* je proces postavljanja neophodnih objekta
  za renderovanje zajedno sa odgovarajucim shader programom za 
  njega, kao i proces koriscenja tih objekata za renderovanje.

## Teorija

* Pruzanje vertex podataka za renderovanje zahteva kreiranje streama
  vertexa, i onda treba reci OpenGLu kako da interpretira taj stream.

### Vertex Stream

* Vertex Shader korisnicki definisane ulazne promenljive su lista
  ocekivanih *vertex atributa* za njega, gde se svaki atribut mapira
  na korisnicki definisan ulaznu promenljivu.
* Red vertexa u strimu je vrlo bita, jer na osnovu njega OpenGL 
  procesuira podatke i renderuje Primitive. Drugi nacin na koji se
  oni renderuju je pomocu liste indeksa koji definisu red.
* Neka su vertexi dati kao 3d pozicije:
```
{ {1, 1, 1}, {0, 0, 0}, {0, 0, 1} }
```
* Ako se one prime kao stream, OpenGL ce ih primiti i procesuirati ih
  po redu od leve ka desnoj.
* Moguce je specifikovati jos jednu listu indeksa koja ce birati
  koji od gornjih vertexa da koristi.
* Neka je lista indeksa data sa:
```
{2, 1, 0, 2, 1, 2}
```
* Onda ce OpenGL dobiti sledeci stream verteksa:
```
{ {0, 0, 1}, {0, 0, 0}, {1, 1, 1}, {0, 0, 1}, {0, 0, 0}, {0, 0, 1} }
```

### Primitive

* Stream kao takav nije dovoljan za renderovanje, mora se navasti
  OpenGLu kako da interpretira taj stream, tj. navasti koju primitivu
  da koristi.
* Postoje mnoge primitive: trouglovi, tacke, linije...
* Primer: Imamo 12 vertexa. 
  * 4 nezavisna trougla, svaka 3 vertexa odgovaraju trouglu
  * 10 zavisnih trougla, svaka groupa od 3 uzastopna vertexa cina    
    trouglo.

## Vertex Array Objekat

* *Vertex Array Objekat (VAO)* je OpenGL objekat koji cuva sva 
  potrebna stanja vertex podataka.
  * Cuva format vertex podataka, kao i Buffer Objekti, pruzajuci 
    vertex data arrays.
  * VAO ne kopira, zamrzava ili cuva same podatke na koje referise.
    * Ako se oni promene preko VAO, one ce biti vidjene i drugim VAO.
* Kako je OpenGL objekat koriste se funkicje
```
glGenVertexArrays, glDeleteVertexArrays, glBindVertexArray
```
* Vertex atributi su oznaceni brojem od ``0`` do 
  ``GL_MAX_VERTEX_ATTRIBS - 1``. 
* Svaki atribut se moze ukljuciti ili iskljuciti za pristup.
  * Kada je iskljucen citanje u vertex shaderu ce proizvesti 
    konstantne vrednosti.
```c
void glEnableVertexAttribArray(GLuint index);
void glDisableVertexAttribArray(GLuint index);
```

## Vertex Buffer Objekat

* *Vertex Buffer Objekat (VBO)* je izraz za normalan Buffer Objekat,
  koji se koristi za izvorne podatke niza vertexa.
* Kada se on napravi i poveze mogu se koristiti sledece funkcije:
```c
void glVertexAttribPointer( GLuint index, GLint size, GLenum type,
   GLboolean normalized, GLsizei stride, const void *offset);
 void glVertexAttribIPointer( GLuint index, GLint size, GLenum type,
   GLsizei stride, const void *offset);
 void glVertexAttribLPointer( GLuint index, GLint size, GLenum type,
   GLsizei stride, const void *offset);
```
* Primer koriscenja:
```c
glBindBuffer(GL_ARRAY_BUFFER, buf1);
glVertexAttribPointer(0, 4, GL_FLOAT, GL_FALSE, 0, 0);
glBindBuffer(GL_ARRAY_BUFFER, 0);
```

## Vertex Format

* ``glVertexAttribPointer`` pokazuje indeksu odakle da dobija 
  podatke. Ali takodje i kako da ih interpretira, tj njihov format.
* Format parametri opisuju kako interpretirati jedan vertex od 
  informacija iz niza. 
* Tip u atributu koji se koristi u vertex shaderu mora se poklopiti
  sa tipom koju koristi ``glVertexAttribPointer`` funkcija.
  * Za float se koristi ``glVertexAttribPointer``
  * Za int se koristi ``glVertexAttribIPointer``
  * Za double se koristi ``glVertexAttribLPointer``
* ``size`` parametar specifikuje boj komponenti vektora koji se
  pruza funkciji.

## Vertex Buffer offset i stride

* Vertex format nije dovoljan za za potpunu informaciju o jednom
  vertexu, jer nam on samo kaze koliko je jedan vertex velik, i kako
  konvertovati njegove vrednosti u atribute.
  * Potreban nam je jos i pocetak baffer objekta tj. njegov prvi
    element (offset). Ali takodje je potrebna i stride, koji 
    predstavlja koliko bajtova ima od pocetka jednog elementa do
    pocetka drugog elementa.
* *offset* definise buffer objekat offset. Mora da se kastuje u 
  ``(void*)`` zbog legacy stvari.
* *stride* se koristi da otkrije da li postoji razmaka izmedju      
  vertexa.
  * Ako je 0, onda ce OpenGL predpostaviti da je sve lepo 
    spakovono. Ako je size 3 i tip ``GL_FLOAT``, onda ce on biti 12.
    (4 bajta po floatu, i 3 floata po atributu).

## Index Buffers

* Indexno renderovanje, opisano gore, zahteva indexe.
* On se pruza kao Buffer Objekat sa targetom 
  ``GL_ELEMENT_ARRAY_BUFFER``.









