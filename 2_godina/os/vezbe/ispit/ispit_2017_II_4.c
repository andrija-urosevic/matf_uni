#define _XOPEN_SOURCE (700)
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <string.h>
#include <ctype.h>

#include <errno.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_SIZE (256)

bool is_num(char* word)
{
    for (int i = 0; word[i]; i++) {
        if (i == 0 && word[i] == '-') {
            continue;
        }
        if (!isdigit(word[i])) {
            return false;
        }
    }

    return true;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    FILE* f = fopen(argv[1], "r");
    check_error(f != NULL, "fdopen");

    int fd = open(argv[1], O_RDWR);
    check_error(fd != -1, "open");

    struct flock fl;

    int count = 0;
    char buf[MAX_SIZE];
    while (fscanf(f, "%s", buf) == 1) {
        if (!is_num(buf)) {
            continue;
        }

        fl.l_type = F_RDLCK;
        fl.l_whence = SEEK_CUR;
        fl.l_start = ftell(f);
        fl.l_len = -strlen(buf);

        int res = fcntl(fd, F_SETLK, &fl);
        if (res == -1) {
            if (errno != EACCES && errno != EAGAIN) {
                check_error(false, "fcntl");
            }
        } else {
            count++;
        }
    }

    printf("%d\n", count);
    
    fclose(f);
    close(fd);
    exit(EXIT_SUCCESS);
}
