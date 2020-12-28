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

void swap(char* word, int n)
{
    int j = n - 1;
    int i = 0;
    while (i < j) {
        char tmp = word[i];
        word[i] = word[j];
        word[j] = tmp;
        i++;
        j--;
    }
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int fd = open(argv[1], O_RDWR);
    check_error(fd != -1, "open");

    FILE* f = fopen(argv[1], "r+");
    check_error(f != NULL, "fopen");

    struct flock fl;

    int count_changed = 0;
    int count_unchanged = 0;

    char buf[MAX_LEN];
    while (fscanf(f, "%s", buf) == 1) {
        int len = strlen(buf);

        fl.l_type = F_WRLCK;
        fl.l_whence = SEEK_CUR;
        fl.l_start = ftell(f);
        fl.l_len = -len;

        check_error(fcntl(fd, F_GETLK, &fl) != -1, "fcntl");
        if (fl.l_type == F_UNLCK) {
            check_error(fseek(f, -len, SEEK_CUR) != -1, "fseek");
            swap(buf, len);
            fprintf(f, "%s", buf);
            count_changed++;
        } else {
            count_unchanged++;
        }
    }

    printf("%d %d\n", count_changed, count_unchanged);

    fclose(f);
    close(fd);
    
    exit(EXIT_SUCCESS);
}
