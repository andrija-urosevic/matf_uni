#include <iostream>

template<typename T>
inline T arithmetic_mean(const T& a, const T& b)
{
    return (a + b) / 2;
}

auto main(void) -> int
{
    std::cout << arithmetic_mean(5, 11) << std::endl;
    std::cout << arithmetic_mean<int>(5, 11) << std::endl;
    std::cout << arithmetic_mean(5.5f, 11.0f) << std::endl;
    std::cout << arithmetic_mean(5.5, 11.0) << std::endl;
    std::cout << arithmetic_mean<double>(5.5, 11.0) << std::endl;

    return 0;
}
