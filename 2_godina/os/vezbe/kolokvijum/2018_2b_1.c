#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

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
    check_error(stat(argv[1], &sb) != -1, "stat");

    printf("%ld\n", (time_t) ceil(difftime(sb.st_atime, sb.st_mtime) / 3600));

    exit(EXIT_SUCCESS);
}
