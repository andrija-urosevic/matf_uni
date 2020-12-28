#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void ispis(const char* pathname, int a, int b)
{
    int fd = open(pathname, O_RDONLY);
    check_error(fd != -1, "open");

    check_error(lseek(fd, a, SEEK_SET) != -1, "lseek");

    char buf[b];
    ssize_t bytes_read = read(fd, buf, b * sizeof (char));
    check_error(bytes_read > 0, "read");
    check_error(write(STDOUT_FILENO, buf, bytes_read) != -1, "write");

    close(fd);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 4, "argumenti");
    errno = 0;

    int a = atoi(argv[2]);
    int b = atoi(argv[3]);

    ispis(argv[1], a, b);

    exit(EXIT_SUCCESS);
}
