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
            exit(EXIT_FAILURE); \
        } \
    } while(0)


int main(int argc, const char *argv[])
{
    check_error(argc == 4, "argumenti");

    const char* path = argv[1];
    off_t a = atoi(argv[2]);
    off_t b = atoi(argv[3]);

    int fd = open(path, O_RDWR);
    check_error(fd != -1, "open");

    struct flock lock;
    lock.l_type = F_WRLCK;
    lock.l_whence = SEEK_CUR;
    lock.l_start = a;
    lock.l_len = b;

    check_error(fcntl(fd, F_GETLK, &lock) != -1, "fcntl");
    if (lock.l_type == F_UNLCK) {
        printf("unlocked\n");
    } else if (lock.l_type == F_RDLCK) {
        printf("shared lock\n");
    } else if (lock.l_type == F_WRLCK) {
        printf("exclusive lock\n");
    }

    close(fd);
    
    exit(EXIT_SUCCESS);
}
