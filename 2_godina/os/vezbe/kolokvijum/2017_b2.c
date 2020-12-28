#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int getsize(const char* pathname, const char* unit)
{
    double factor;
    if (strcmp(unit, "KB") == 0) {
        factor =  pow(2, 10);
    } else if (strcmp(unit, "MB") == 0) {
        factor =  pow(2, 20);
    } else if (strcmp(unit, "GB") == 0) {
        factor = pow(2, 30);
    } else {
        check_error(-1, "unit");
    }

    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");

    return ceil(sb.st_size / factor);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    int size = getsize(argv[1], argv[2]);
    char* filename = strrchr(argv[1], '/');
    if (filename != NULL) {
        printf("%s ", filename + 1);
    } else {
        printf("%s ", argv[1]);
    }
    printf("%d%s\n", size, argv[2]);

    exit(EXIT_SUCCESS);
}
