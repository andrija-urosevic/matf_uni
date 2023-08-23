# Konvencija Imenovanja

**Zasto?** Izvorni kod citaju ljudi!

### PascalCase

* Prvo slovo veliko.
* Svako prvo slovo nove reci veliko.
* Ostala slova malo.

### camelCase

* Prvo slovo malo.
* Svako prvo slovo nove reci veliko.
* Ostala slova malo.

### snake_case

* Sva slova su mala.
* Razmaci se zamenjuju sa donjom crtom: `_`.

## Imena klasa

* PascalCase
* Obicno su to imenice.

```
class MyClass {};
```

## Prefiksi imena

* prefiks `m` oznacava member promenljivu.
* prefiks `s` oznacava promenljivu koja je static.
* prefiks `p` oznacava pokazivac.
* prefiks `r` oznacava referencu, koja moze da se menja, tj. nije konstantna.
* prefiks `I` oznacava intefrejs.

## Imena metoda

* PascalCase
* Obicno su to glagoli.
* Sufiksi kao sto je `Max`, `Key`, `Count` su pozeljni.
* Prefiksi kao sto su `Get`, `Set`, `Is`, has su pozeljni.
* Parametri funkcija su camelCase

```
void GetVarName;
T SetVarName(T varName);
```

## Imena polja

* camelCase

```
class MyClass 
{
public:
    ...
private:
    double m_positionX;                     // member
    double m_positionY;                     // member
    
    static float ms_speedFactor = 0.5f;     // static member
public:
    static int s_myClassInstancesCount = 0; // static
};
```

## Imena funkcija

* snake_case
* Odnosi se na funkcije koje nisu unutar neke klase, tj. nisu metode klase.
* Parametri su takodje snake_case.


## Imena promenljivih

* snake_case
* Odnosi se na promenljive koje su na steku ili globalne promenljive.

## Globalne konstante

* ALL CAPS, gde je `_` umesto razmaka.

```
const size_t MAX_LIST_SIZE = 10000;
```

## Namespace

* PascalCase

### Primer:

```
#pragma once

namespace NamingConvention {

    class MyNamingConvention
    {
        public:
            MyNamingConvention();
            MyNamingConvention(bool usePrefixes,
                               Style classNameStyle,
                               Style fieldVarStyle,
                               Style methodStyle,
                               Style functionStyle,
                               Style varStyle)
                : m_classNameStyle(classNameStyle)
                , m_fieldVarStyle(fieldVarStyle)
                , m_methodStyle(methodStyle)
                , m_functionStyle(functionStyle)
                , m_varStyle(varStyle)
            { };

            ~MyNamingConvention();

            void SetClassNameStyle(Style classNameStyle)
            {
                m_classNameStyle = classNameStyle;
            };

            Style GetClassNameStyle()
            {
                return m_classNameStyle;
            };

            String printStyle()
            {
                std::vector<Style> styles = {
                    m_classNameStyle,
                    m_functionStyle,
                    m_methodStyle,
                    m_functionStyle,
                    m_varStyle,
                }

                std::string result = "";
                for (auto style : styles) {
                    result.append(style)
                }

                return result;
            };

        private:
            bool m_usePrefixes;
            Style m_classNameStyle;
            Style m_fieldVarStyle;
            Style m_methodStyle;
            Style m_functionStyle;
            Style m_varStyle;
    };

};
```
