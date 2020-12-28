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


int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 4, "argumenti");
    errno = 0;

    mode_t mode = strtol(argv[3], NULL, 8);
    mode_t old_umask = umask(0);

    if (argv[1][1] == 'f') {
        int fd = open(argv[2], O_WRONLY | O_CREAT | O_EXCL, mode);
        check_error(fd != -1, "greska");
        close(fd);
    } else if (argv[1][1] == 'd') {
        check_error(mkdir(argv[2], mode) != -1, "mkdir");
    } else {
        check_error(-1, "-f/-d");
    }

    umask(old_umask);

    exit(EXIT_SUCCESS);
}
