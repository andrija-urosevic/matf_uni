#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <limits.h>

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
    check_error(lstat(argv[1], &sb) != -1, "lstat");
    check_error(S_ISREG(sb.st_mode), "nije reg");

    int fd = open(argv[2], O_CREAT);
    check_error(fd != -1, "open");

    char* path1 = realpath(argv[1], NULL);
    char* path2 = realpath(argv[2], NULL);
    check_error(strcmp(path1, path2), "isti su");
    check_error(rename(path1, path2) != -1, "rename");


    exit(EXIT_SUCCESS);
}
