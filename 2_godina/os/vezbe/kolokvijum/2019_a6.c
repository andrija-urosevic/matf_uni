#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>

#define MAX_SIZE 1024

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void ispis(const char *pathname)
{
    struct stat sb;
    check_error(lstat(pathname, &sb) != -1, "stat");
    check_error(S_ISLNK(sb.st_mode), "not link");

    char* buf = malloc(MAX_SIZE);
    ssize_t bytes_read = readlink(pathname, buf, MAX_SIZE);
    check_error(bytes_read > 0, "readlink");
    check_error(write(STDOUT_FILENO, buf, bytes_read) != -1, "write");
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    ispis(argv[1]);


    exit(EXIT_SUCCESS);
}
