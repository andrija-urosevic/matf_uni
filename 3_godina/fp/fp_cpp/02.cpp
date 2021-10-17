#include <iostream>
#include <vector>
#include <numeric>
#include <functional>
#include <algorithm>

typedef struct{
    std::string name;
    char gender;
} person_t;

bool is_female(const person_t& person)
{
    return person.gender == 'f';
}

bool is_not_female(const person_t& person)
{
    return person.gender != 'f';
}

std::string name(const person_t& person)
{
    return person.name;
}

std::vector<person_t> filter_females(const std::vector<person_t>& people) 
{
    std::vector<person_t> females;

    std::copy_if(
            people.cbegin(), people.cend(),
            std::back_inserter(females),
            is_female
    );

    return females;
}

std::vector<std::string> get_names(const std::vector<person_t>& people)
{
    std::vector<std::string> names(people.size());

    std::transform(
            people.cbegin(), people.cend(),
            names.begin(),
            name
    );

    return names;
}

std::vector<std::string> get_female_names(const std::vector<person_t>& people) 
{
    return get_names(filter_females(people));
}

std::vector<person_t> partition_females(const std::vector<person_t>& people)
{
    std::vector<person_t> separated(people.size());

    const auto last = std::copy_if(
            people.cbegin(), people.cend(),
            separated.begin(),
            is_female
    );

    std::copy_if(
            people.cbegin(), people.cend(),
            last,
            is_not_female
    );

    return separated;
}

double average_score(const std::vector<int>& scores)
{
    return std::accumulate(
            scores.cbegin(), scores.cend(),
            0
    ) / (double) scores.size();
}

double product_score(const std::vector<int>& scores)
{
    return std::accumulate(
            scores.cbegin(), scores.cend(),
            1,
            std::multiplies<int>()
    );
}

int count_lines(const std::string& str)
{
    return std::accumulate(
            str.cbegin(), str.cend(),
            0,
            [](int acc, char c) { 
                return (c == '\n') ? acc + 1 : acc; 
            }
    );
}

std::string trim_left(std::string s)
{
    s.erase(s.begin(),
            std::find_if(
                s.begin(), s.end(), 
                [](char c) {
                    return c != ' ';
                }
            )
    );

    return s;
}

std::string trim_right(std::string s)
{
    s.erase(std::find_if(
                s.rbegin(), s.rend(), 
                [](char c) {
                    return c != ' ';
                }
            ).base(),
            s.end()
    );
    return s;
}

std::string trim(std::string s)
{
    return trim_left(trim_right(std::move(s)));
}

std::vector<int> odd_first(std::vector<int> vec)
{
    std::partition(
            vec.begin(), vec.end(),
            [](int elem) { return elem % 2 != 0; }
    );

    return vec;
}

template <class InputIt, class UnaryPredicate>
bool any_of_(InputIt first, InputIt last, UnaryPredicate p)
{
    return std::accumulate(
            first, last,
            false,
            [p](bool acc, auto it) {
                return acc || p(it);
            }
    );
}

template <class InputIt, class UnaryPredicate>
bool all_of_(InputIt first, InputIt last, UnaryPredicate p)
{
    return std::accumulate(
            first, last,
            true,
            [p](bool acc, auto it) {
                return acc && p(it);
            }
    );
}

template <class InputIt, class UnaryPredicate>
InputIt find_if_(InputIt first, InputIt last, UnaryPredicate p)
{
    return std::accumulate(
            first, last,
            std::make_pair(last, 0),
            [p, first, last](auto acc, auto it) {
                return p(it) && acc.first == last ? std::make_pair(first + acc.second, acc.second)
                                                  : std::make_pair(acc.first, acc.second + 1);
            }
    ).first;
}

template <typename T>
int count_ajd_equals(const T& xs)
{
    return std::inner_product(
            xs.begin() + 1, xs.end(),
            xs.begin(),
            0,
            std::plus<>(),
            std::equal_to<>()
    );
}

bool is_even(int val)
{
    return val % 2 == 0;
}

int main(int argc, const char *argv[])
{
    std::string text = "neekii teekkstt";
    std::cout << count_ajd_equals(text) << std::endl;

    std::vector<int> vec = { 1, 4, 2, 1, 1, 3, 3, 5 };
    std::cout << count_ajd_equals(vec) << std::endl;

    std::vector<int> scores = { 9, 7, 10, 5, 8, 8, 6 };
    std::cout << average_score(scores) << std::endl;
    std::cout << product_score(scores) << std::endl;

    std::string str = "Neki tekst.\nOvo je interesantno.\nFP je zakon!\n";
    std::cout << count_lines(str) << std::endl;

    std::cout << trim("   Neki tekst    ") << std::endl;

    auto v = odd_first(std::move(vec));
    for (int it : v) {
        std::cout << it << " ";
    }
    std::cout << std::endl;

    std::vector<person_t> people = {
        {"Mara", 'f'},
        {"Mira", 'f'},
        {"Pera", 'm'},
        {"Zika", 'z'},
        {"Jana", 'f'}
    };
    std::cout << "Particionisani ljudi: (Zene, Muskarci)" << std::endl;
    std::vector<person_t> separated = partition_females(people);
    for (auto it : separated) {
        std::cout << it.name << std::endl;
    }

    std::cout << "Imena zena: " << std::endl;
    std::vector<std::string> female_names = get_female_names(people);
    for (auto it : female_names) {
        std::cout << it << std::endl;
    }

    std::vector<int> v1 = { 2, 4, 6, 8 };
    std::vector<int> v2 = { 1, 3, 5, 2, 9 };

    std::cout << all_of_(v1.begin(), v1.end(), is_even) << std::endl;
    std::cout << any_of_(v2.begin(), v2.end(), is_even) << std::endl;
    std::cout << *find_if_(v2.begin(), v2.end(), is_even) << std::endl;
    
    return 0;
}

