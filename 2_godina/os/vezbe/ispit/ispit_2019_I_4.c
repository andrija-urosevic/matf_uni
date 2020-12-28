#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>
#include <wait.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_LEN 256
#define RD_END 0
#define WR_END 1

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int fd = open(argv[1], O_RDONLY);
    check_error(fd != -1, "open");

    FILE* f = fdopen(fd, "r");
    check_error(f != NULL, "fdopen");


    ssize_t max_bytes = 0;
    char* line = NULL;
    char max_line[MAX_LEN];
    size_t size = 0;

    while(getline(&line, &size, f) != -1) {
        char cmp[MAX_LEN];
        char arg[MAX_LEN];
        sscanf(line, "%s %s", cmp, arg);

        int cld2par[2];
        check_error(pipe(cld2par) != -1, "pipe");

        pid_t pid = fork();
        check_error(pid != -1, "fork");
        if (pid == 0) {
            close(cld2par[RD_END]);

            check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");

            check_error(execlp(cmp, cmp, arg, NULL) != -1, "execlp");
            
            exit(EXIT_SUCCESS);
        } else {
            close(cld2par[WR_END]);

            char buffer[MAX_LEN];
            ssize_t bytes = 0;
            ssize_t bytes_read = 0;
            while ((bytes_read = read(cld2par[RD_END], buffer, MAX_LEN)) > 0) {
                bytes += bytes_read;
            }
            check_error(bytes_read != -1, "read");

            if (max_bytes < bytes) {
                max_bytes = bytes;
                strcpy(max_line, line);
            }
        }
        wait(NULL);
    }

    printf("%s", max_line);
    
    free(line);
    fclose(f);
    close(fd);
    exit(EXIT_SUCCESS);
}
