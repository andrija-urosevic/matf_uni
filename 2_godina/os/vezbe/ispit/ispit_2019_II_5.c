#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <ctype.h>
#include <errno.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_LEN (256)

bool is_num(char* word)
{
    int i = 0;
    while (word[i]) {
        if (i > 4 || !isdigit(word[i])) {
            return false;
        }
        i++;
    }

    return i == 4;
}

int main(int argc, const char *argv[])
{
    FILE* f = fopen(argv[1], "r+");
    check_error(f != NULL, "fopen");

    int fd = open(argv[1], O_RDWR);
    check_error(fd != -1, "open");

    struct flock fl;

    char buf[MAX_LEN];
    while (fscanf(f, "%s", buf) == 1) {
        if (!is_num(buf)) {
            continue;
        }

        fl.l_type = F_WRLCK;
        fl.l_whence = SEEK_CUR;
        fl.l_start = ftell(f);
        fl.l_len = -4;

        if (fcntl(fd, F_SETLK, &fl) == -1) {
            if (errno == EACCES || errno == EAGAIN) {
                continue;
            } else {
                check_error(-1, "fcntl");
            }
        } else { /* Lock was granted... */
            check_error(fseek(f, -4, SEEK_CUR) != -1, "fseek");
            fprintf(f, "####");

            fl.l_type = F_UNLCK;
            fl.l_whence = SEEK_CUR;
            fl.l_start = ftell(f);
            fl.l_len = -4;
            check_error(fcntl(fd, F_SETLK, &fl) != -1, "fcntl");
        }
    }

    close(fd);
    fclose(f);
    exit(EXIT_SUCCESS);
}
