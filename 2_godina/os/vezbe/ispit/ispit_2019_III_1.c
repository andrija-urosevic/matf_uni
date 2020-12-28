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


int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    const time_t t = (time_t) atoi(argv[1]);
    struct tm* tb = localtime(&t);

    if (tb->tm_hour <= 6) {
        printf("noc\n");
    } else if (tb->tm_hour <= 8) {
        printf("jutro\n");
    } else if (tb->tm_hour <= 11) {
        printf("prepodne\n");
    } else if (tb->tm_hour <= 18) {
        printf("popodne\n");
    } else {
        printf("vece\n");
    }

    
    exit(EXIT_SUCCESS);
}
