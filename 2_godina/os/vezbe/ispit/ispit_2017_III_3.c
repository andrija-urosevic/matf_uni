#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include <errno.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_SIZE 256

int main(int argc, const char *argv[])
{
    check_error(argc == 4, "argumenti");

    int fd = open(argv[1], O_RDWR);
    check_error(fd != -1, "open");

    FILE* f = fopen(argv[1], "r+");
    check_error(f != NULL, "fopen");

    struct flock fl;

    int count = 0;
    char buf[MAX_SIZE];
    while (fscanf(f, "%s", buf) == 1) {
        if (strcmp(buf, argv[2]) != 0) {
            continue;
        }

        fl.l_type = F_WRLCK;
        fl.l_whence = SEEK_CUR;
        fl.l_start = ftell(f);
        fl.l_len = -strlen(buf);

        if (fcntl(fd, F_SETLK, &fl) == -1) {
            if (errno = EACCES || errno == EAGAIN) {
                count++;
            } else {
                check_error(false, "fcntl");
            }
        } else {
            fseek(f, -strlen(buf) ,SEEK_CUR);
            fprintf(f, "%s", argv[3]);
        }
    }
    printf("%d\n", count);
    
    fclose(f);
    close(fd);
    exit(EXIT_SUCCESS);
}
