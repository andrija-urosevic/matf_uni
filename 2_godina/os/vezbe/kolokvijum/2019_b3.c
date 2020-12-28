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
            perror(usermsg); \
        } \
    } while (0);

void zameni(const char* pathname, int p, int n)
{
    int fd = open(pathname, O_RDWR);
    check_error(fd != -1, "open");

    check_error(lseek(fd, p, SEEK_SET) != -1, "lseek");
    char* buf = malloc(n * sizeof (char));
    int bytes_read = 0;
    if ((bytes_read = read(fd, buf, n * sizeof (char))) > 0) {
        int j = strlen(buf) - 1;
        int i = 0;
        while (i < j) {
            char tmp = buf[i];
            buf[i] = buf[j];
            buf[j] = tmp;
            i++;
            j--;
        }
        check_error(lseek(fd, p, SEEK_SET) != -1, "lseek");
        if (write(fd, buf, bytes_read) == -1) {
            free(buf);
            exit(EXIT_FAILURE);
        }
    } else {
        free(buf);
        exit(EXIT_FAILURE);
    }
    
    free(buf);
    close(fd);
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
