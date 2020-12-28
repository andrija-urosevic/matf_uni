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

void mkpubdir(const char* pathname)
{
    mode_t old_umask = umask(0);
    mode_t mode = 0777;

    check_error(mkdir(pathname, mode) != -1, "mkdir");

    umask(old_umask);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    mkpubdir(argv[1]);

    exit(EXIT_SUCCESS);
}
