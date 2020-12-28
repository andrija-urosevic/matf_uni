#define _XOPEN_SOURCE (700)
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <limits.h> 
#include <string.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc > 1, "argumenti");
    errno = 0;

    struct stat sb;
    for (int i = 1; i < argc; i++) {
        check_error(stat(argv[i], &sb) != -1, "stat");

        check_error(S_ISDIR(sb.st_mode), "nije dir");

        if (sb.st_mode % 8 == 0) {
            char* path = realpath(argv[i], NULL);
            check_error(path != NULL, "realpath");
            printf("%d\n", strlen(path));
            free(path);
        }
    }

    exit(EXIT_SUCCESS);
}
