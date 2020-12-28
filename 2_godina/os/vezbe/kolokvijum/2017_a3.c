#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void change_mode(const char* pathname, const char type, mode_t mode)
{
    if (type == 'f') {
        int fd = open(pathname, O_CREAT, mode);
        check_error(fd != -1, "open");
        close(fd);
    } else {
        int md = mkdir(pathname, mode);

        if (md != -1) {
            check_error(errno != EEXIST, "postoji");
        }
    }

    check_error(chmod(pathname, mode) != -1, "chmod"); 
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 4, "argumenti");
    errno = 0;

    change_mode(argv[2], argv[1][1], strtol(argv[3], NULL, 8));

    exit(EXIT_SUCCESS);
}
