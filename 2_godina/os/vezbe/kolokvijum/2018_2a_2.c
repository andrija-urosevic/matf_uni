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

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat");
    check_error(S_ISDIR(sb.st_mode), "not dir");

    int n = sizeof (argv[1]) / sizeof (char);
    char* pathname = malloc(n * sizeof (char) + 1 + sizeof (argv[2]));
    check_error(pathname != NULL, "malloc");
    strcpy(pathname, argv[1]);

    while (n > 0 && pathname[n] != '/') {
        n--;
    }
    pathname[n] = '\0';
    if (n != 0) {
        strcat(pathname, "/");
    }
    strcat(pathname, argv[2]);


    check_error(rename(argv[1], pathname) != -1, "rename");

    free(pathname);

    exit(EXIT_SUCCESS);
}
