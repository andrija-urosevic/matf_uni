#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>

#include <errno.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)


// ./lock pathname intervals
int main(int argc, const char *argv[])
{
    check_error(argc == 3, "argumenti");

    int fd = open(argv[1], O_RDWR);
    check_error(fd != -1, "open");


    FILE* f = fopen(argv[2], "r");
    check_error(f != NULL, "fopen");

    struct flock lock;

    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        lock.l_type = F_WRLCK;
        lock.l_whence = SEEK_CUR;
        lock.l_start = a;
        lock.l_len = b;

        check_error(fcntl(fd, F_SETLK, &lock) != -1, "fcntl");
    }

    char c;
    do {
        c = getchar();
    } while (c != 'n');
    
    fclose(f);
    close(fd);
    exit(EXIT_SUCCESS);
}
