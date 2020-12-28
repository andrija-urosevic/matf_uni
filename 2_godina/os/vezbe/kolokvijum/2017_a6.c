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
            perror(usermsg); \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    struct stat sb;
    if (lstat(argv[2], &sb) == -1 && errno == ENOENT) {
        check_error(lstat(argv[1], &sb) != -1, "lstat");
        if (S_ISDIR(sb.st_mode)) {
            check_error(mkdir(argv[2], 0755) != -1, "mkdir");
        } else {
            int fd = open(argv[2], O_CREAT, 0755);
            check_error(fd != -1, "open");
            close(fd);
        }
    }

    const char* path1 = realpath(argv[1], NULL);
    const char* path2 = realpath(argv[2], NULL);

    check_error(strcmp(path1, path2), "isti su");
    check_error(rename(path1, path2) != -1, "rename");

    exit(EXIT_SUCCESS);
}
