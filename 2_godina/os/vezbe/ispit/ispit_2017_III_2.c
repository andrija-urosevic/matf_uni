#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/wait.h>
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

#define RD_END (0)
#define WR_END (1)

int main(int argc, char *argv[])
{
    check_error(argc == 2, "argumenti");

    strcat(argv[1], "\n");

    int cld2par[2];
    check_error(pipe(cld2par) != -1, "pipe");

    pid_t pid = fork();
    check_error(pid != -1, "fork");

    int count = 0;

    if (pid == 0) {
        close(cld2par[RD_END]);

        check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");
        check_error(execlp("find", "find", ".", "-type", "f", NULL) != -1, "execlp");

        close(cld2par[WR_END]);
        _exit(EXIT_SUCCESS);
    } else {
        close(cld2par[WR_END]);
        int status;
        check_error(wait(&status) != -1, "wait");

        FILE* f = fdopen(cld2par[RD_END], "r");
        check_error(f != NULL, "fdopen");

        char *buf = NULL;
        size_t n = 0;
        while (getline(&buf, &n, f) != -1) {
            char* ext = strrchr(buf, '.');
            if (ext == NULL) {
                continue;
            }

            if (strcmp(ext, argv[1]) == 0) {
                count++;
            }
        }

        fclose(f);
        close(cld2par[RD_END]);
    }

    printf("%d\n", count);
    
    exit(EXIT_SUCCESS);
}
