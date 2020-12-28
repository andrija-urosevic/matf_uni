#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void ispis(const char* pathname1, const char* pathname2)
{
    struct stat sb;

    check_error(stat(pathname1, &sb) != -1, "stat");
    time_t mtime1 = sb.st_mtime;

    check_error(stat(pathname2, &sb) != -1, "stat");
    time_t mtime2 = sb.st_mtime;

    if (mtime1 > mtime2) {
        char* filename = strrchr(pathname1, '/');
        if (filename != NULL) {
            printf("%s\n", filename + 1);
        } else {
            printf("%s\n", pathname1);
        }
    } else {
        char* filename = strrchr(pathname2, '/');
        if (filename != NULL) {
            printf("%s\n", filename + 1);
        } else {
            printf("%s\n", pathname2);
        }
    }
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    ispis(argv[1], argv[2]);

    exit(EXIT_SUCCESS);
}
