#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>

#include <errno.h>
#include <time.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

void print_month(int mon)
{
    switch (mon) {
        case 0:
            printf("januar ");
            break;
        case 1:
            printf("februar ");
            break;
        case 2:
            printf("mart ");
            break;
        case 3:
            printf("april ");
            break;
        case 4:
            printf("maj ");
            break;
        case 5:
            printf("jun ");
            break;
        case 6:
            printf("jul ");
            break;
        case 7:
            printf("avgust ");
            break;
        case 8:
            printf("septembar ");
            break;
        case 9:
            printf("oktobar ");
            break;
        case 10:
            printf("novembar ");
            break;
        case 11:
            printf("decembar ");
            break;
    }
}

int main(int argc, const char *argv[])
{
    check_error(argc == 3, "argumenti");

    time_t ttime = (time_t) atoi(argv[1]);
    int days_in_sec = atoi(argv[2]) * 24 * 60 * 60;

    struct tm* t;

    t = localtime(&ttime);
    print_month(t->tm_mon);
    
    ttime += days_in_sec;
    t = localtime(&ttime);
    print_month(t->tm_mon);
    
    exit(EXIT_SUCCESS);
}
