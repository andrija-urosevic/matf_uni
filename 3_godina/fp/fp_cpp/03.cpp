#include <iostream>
#include <string>
#include <numeric>
#include <algorithm>


typedef struct{
    std::string name;
    char gender;
} person_t;


int old_max(int arg1, int arg2)
{
    return arg1 > arg2 ? arg1 : arg2;
}

auto new_max(int arg1, int arg2) -> int
{
    return arg1 > arg2 ? arg1 : arg2;
}

auto factorial(int n)
{
    if (n == 0) {
        return 1;
    }
    return n * factorial(n - 1);
}

int main(int argc, const char *argv[])
{
    std::cout << old_max(3, 6) << std::endl;
    std::cout << new_max(3, 6) << std::endl;
    
    return 0;
}
