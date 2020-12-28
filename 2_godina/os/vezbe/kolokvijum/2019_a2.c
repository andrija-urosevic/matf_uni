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

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(lstat(argv[1], &sb) != -1, "stat");
    check_error(S_ISLNK(sb.st_mode), "nije link");

    printf("%ld\n", sb.st_mtime);


    exit(EXIT_SUCCESS);
}
