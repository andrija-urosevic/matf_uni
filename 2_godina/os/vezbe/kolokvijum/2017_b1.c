#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

#define DAYS_IN_SEC (60 * 60 * 24)

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void diff_time(const char* pathname)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");
    check_error(S_ISREG(sb.st_mode), "stat");

    time_t diff_time = (time_t)
        difftime(sb.st_atime, sb.st_mtime) / DAYS_IN_SEC;
    printf("%d\n", diff_time);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    diff_time(argv[1]);


    exit(EXIT_SUCCESS);
}
