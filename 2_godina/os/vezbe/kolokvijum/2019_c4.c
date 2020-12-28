#define _XOPEN_SOURCE 700
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

void napravi(const char* pathname1, const char* pathname2, 
             const char* new_pathname)
{
    struct stat sb;

    check_error(stat(pathname1, &sb) != -1, "stat");
    mode_t mode1 = sb.st_mode;

    check_error(stat(pathname2, &sb) != -1, "stat");
    mode_t mode2 = sb.st_mode;

    mode_t new_mode = 0;
    new_mode |= S_IFREG;
    new_mode |= (mode1 & mode2) & ~S_IFMT;

    mode_t old_umask = umask(0);

    int fd = open(new_pathname, O_CREAT, new_mode);
    check_error(fd != -1, "open");
    close(fd);

    umask(old_umask);
}
int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 4, "argumenti");
    errno = 0;

    napravi(argv[1], argv[2], argv[3]);

    exit(EXIT_SUCCESS);
}
