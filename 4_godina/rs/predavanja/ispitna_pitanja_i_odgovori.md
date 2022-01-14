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






