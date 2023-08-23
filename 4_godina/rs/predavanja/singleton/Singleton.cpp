#include <iostream>

class Singleton
{
public:

    static Singleton& GetInstance()
    {
        static Singleton instance{};
        return instance;
    };

    // Singleton methods
    void Print()
    {
        std::cout << "Ja sam singleton " << ++m_count << std::endl;
    };

public:
    Singleton(const Singleton&) = delete;
    Singleton& operator=(const Singleton&) = delete;

private:
    Singleton() {};

private:
    int m_count = 0;

};


int main(void)
{
    Singleton::GetInstance().Print();
    Singleton::GetInstance().Print();
    Singleton::GetInstance().Print();

    Singleton& s = Singleton::GetInstance();
    s.Print();
    s.Print();
    
    return 0;
}
