#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void zameni(const char* pathname, int p, int n)
{
    int fd = open(pathname, O_RDWR);
    check_error(fd != -1, "open");

    check_error(lseek(fd, p, SEEK_SET) != -1, "lseek");
    char* buf = malloc(n * sizeof (char));
    n = read(fd, buf, n * sizeof (char)) / sizeof (char);
    check_error(n > 0, "read");

    for (int i = 0; i < n; i++) {
        if (islower(buf[i])) {
            buf[i] = toupper(buf[i]);
        } else if (isupper(buf[i])) {
            buf[i] = tolower(buf[i]);
        }
    }

    check_error(lseek(fd, p, SEEK_SET) != -1, "lseek");
    check_error(write(fd, buf, n * sizeof (char)) > 0, "write");
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 4, "argumenti");
    errno = 0;

    int p = atoi(argv[2]);
    int n = atoi(argv[3]);

    zameni(argv[1], p, n);

    exit(EXIT_SUCCESS);
}
