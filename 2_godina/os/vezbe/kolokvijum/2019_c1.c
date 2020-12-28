#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            perror(usermsg); \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

#define SEC_IN_DAY (60 * 60 * 24)

long int razlika_modifikacija(const char* pathname1, const char* pathname2)
{
    struct stat sb;

    check_error(stat(pathname1, &sb) != -1, "stat");
    time_t t1 = sb.st_mtime;

    check_error(stat(pathname2, &sb) != -1, "stat");
    time_t t2 = sb.st_mtime;

    return ceil((double) abs((long int) difftime(t1, t2)) / SEC_IN_DAY);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    printf("%d\n", razlika_modifikacija(argv[1], argv[2]));

    exit(EXIT_SUCCESS);
}
