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

long int difsize(const char* pathname)
{
    struct stat sb;

    check_error(lstat(pathname, &sb) != -1, "stat");
    check_error(S_ISLNK(sb.st_mode), "nije lnk");
    off_t linksize = sb.st_size;

    check_error(stat(pathname, &sb) != -1, "stat");
    off_t filesize = sb.st_size;

    return filesize - linksize;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    printf("%ld\n", difsize(argv[1]));

    exit(EXIT_SUCCESS);
}
