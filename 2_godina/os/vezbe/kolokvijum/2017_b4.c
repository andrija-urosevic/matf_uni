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

void ispis(const char* pathname, int offset, size_t len)
{
    int fd = open(pathname, O_RDONLY);
    check_error(fd != -1, "open");

    check_error(lseek(fd, offset, SEEK_SET) != -1, "lseek");

    char* buf = malloc(len * sizeof (char));
    ssize_t read_bytes;
    check_error((read_bytes = read(fd, buf, len)) > 0, "read");

    check_error(write(STDOUT_FILENO, buf, read_bytes) != -1, "write");
    free(buf);
    close(fd);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 4, "argumenti");
    errno = 0;

    ispis(argv[1], atoi(argv[2]), atoi(argv[3]));

    exit(EXIT_SUCCESS);
}
