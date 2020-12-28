#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LEN (1024 * sizeof (char))

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void obradi_file(const char* pathname, char op)
{
    char *buf = malloc(MAX_LEN);
    check_error(buf != NULL, "malloc");

    if (op == 'r') {
        int fd = open(pathname, O_RDONLY);
        check_error(fd != -1, "open");

        ssize_t bytes_read;
        while ((bytes_read = read(fd, buf, MAX_LEN)) > 0) {
            check_error(write(STDOUT_FILENO, buf, bytes_read) > 0, "write");
        }
        check_error(bytes_read != -1, "read");

        close(fd);
    } else if (op == 'w') {
        int fd = open(pathname, O_WRONLY | O_CREAT | O_TRUNC, 0755);
        check_error(fd != -1, "open");

        ssize_t bytes_read;
        while ((bytes_read = read(STDIN_FILENO, buf, MAX_LEN)) > 0) {
            check_error(write(fd, buf, bytes_read) > 0, "write");
        }
        check_error(bytes_read != -1, "read");

        close(fd);
    } else if (op == 'a') {
        int fd = open(pathname, O_WRONLY | O_CREAT | O_APPEND, 0755);
        check_error(fd != -1, "open");

        ssize_t bytes_read;
        while ((bytes_read = read(STDIN_FILENO, buf, MAX_LEN)) > 0) {
            check_error(write(fd, buf, bytes_read) > 0, "write");
        }
        check_error(bytes_read != -1, "read");

        close(fd);
    }

    free(buf);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    char op;
    if (strcmp(argv[1], "-r") == 0) {
        op = 'r';
    } else if (strcmp(argv[1], "-w") == 0) {
        op = 'w';
    } else if (strcmp(argv[1], "-a") == 0) {
        op = 'a';
    } else {
        check_error(-1, "opcija");
    }

    obradi_file(argv[2], op);

    exit(EXIT_SUCCESS);
}
