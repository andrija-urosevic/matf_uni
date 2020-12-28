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

#define MAX_LEN (256)

int main(int argc, const char *argv[])
{
    check_error(argc == 3, "argumenti");

    int fd = open(argv[1], O_RDONLY);
    check_error(fd != -1, "open");

    FILE* f = fopen(argv[1], "r");
    check_error(f != NULL, "fopen");

    struct flock fl;

    int len = strlen(argv[2]);

    char buf[MAX_LEN];
    while (fscanf(f, "%s", buf) == 1) {
        if (strcmp(buf, argv[2]) != 0) {
            continue;
        }
        fl.l_type = F_WRLCK;
        fl.l_whence = SEEK_CUR;
        fl.l_start = ftell(f);
        fl.l_len = -len;

        check_error(fcntl(fd, F_GETLK, &fl) != -1, "fcntl");

        if (fl.l_type == F_UNLCK) {
            continue;
        }

        if (fl.l_type == F_WRLCK) {
            printf("%d %c\n", ftell(f) - len, 'w');
        }
        if (fl.l_type == F_RDLCK) {
            printf("%d %c\n", ftell(f) - len, 'r');
        }
    }

    fclose(f);
    close(fd);
    
    exit(EXIT_SUCCESS);
}
