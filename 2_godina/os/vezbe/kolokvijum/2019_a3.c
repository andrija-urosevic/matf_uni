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

void zameni(const char* pathname, int a, int b, int n)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");

    int fd = open(pathname, O_RDWR);
    check_error(fd != -1, "open");
    
    char str_a[n];
    char str_b[n];

    check_error(lseek(fd, a, SEEK_SET) != -1, "lseek");
    int bytes_read_a = read(fd, str_a, n * sizeof (char));
    check_error(bytes_read_a > 0, "read");

    check_error(lseek(fd, b, SEEK_SET) != -1, "lseek");
    int bytes_read_b = read(fd, str_b, n * sizeof (char));
    check_error(bytes_read_b > 0, "read");

    check_error(lseek(fd, a, SEEK_SET) != -1, "lseek");
    check_error(write(fd, str_b, n * sizeof (char)) != -1, "write");

    check_error(lseek(fd, b, SEEK_SET) != -1, "lseek");
    check_error(write(fd, str_a, n * sizeof (char)) != -1, "write");
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 5, "argumenti");
    errno = 0;

    int a = atoi(argv[2]);
    int b = atoi(argv[3]);
    int n = atoi(argv[4]);

    zameni(argv[1], a, b, n);

    exit(EXIT_SUCCESS);
}
