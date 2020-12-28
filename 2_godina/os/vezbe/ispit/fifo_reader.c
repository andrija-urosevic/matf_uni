#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_SIZE 1024

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int fd = open(argv[1], O_RDONLY);
    check_error(fd != -1, "open");

    char buf[MAX_SIZE];
    do {
        ssize_t read_bytes = read(fd, buf, MAX_SIZE);
        check_error(read_bytes != -1, "read");
        if (read_bytes == 0) {
            break;
        }
        buf[read_bytes] = 0;

        int count = 0;
        for (int i = 0; buf[i]; i++) {
            if (buf[i] == 'a') {
                count++;
            }
        }

        printf("%d\n", count);
    } while (1);

    close(fd);
    exit(EXIT_SUCCESS);
}
