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
#define MAX_SIZE (1024)

int main(int argc, const char *argv[])
{
    check_error(argc == 1, "argumenti");

    int cld2par[2];
    check_error(pipe(cld2par) != -1, "pipe");

    pid_t pid = fork();
    check_error(pid != -1, "fork");

    if (pid == 0) {
        close(cld2par[RD_END]);
        check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");
        check_error(execlp("ls", "ls", "-l", NULL) != -1, "execlp");
        close(cld2par[WR_END]);
        _exit(EXIT_SUCCESS);
    } else {
        close(cld2par[WR_END]);
        int status;
        check_error(wait(&status) != -1, "wait");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
            printf("neuspeh\n");
            exit(WEXITSTATUS(status));
        }

        FILE* f = fdopen(cld2par[RD_END], "r");
        check_error(f != NULL, "fdopen");

        char* line = NULL;
        ssize_t size = 0;
        while (getline(&line, &size, f) > 0) {
            char* filename = strrchr(line, ' ');
            if (filename == NULL) {
                continue;
            } else {
                filename++;
            }
            char* permition = strchr(line, ' ') - 3;
            permition[3] = 0;
            if (permition == NULL) {
                continue;
            }
            if (strcmp(permition, "rwx") == 0) {
                printf("%s", filename);
            }
        }

        free(line);
        close(cld2par[RD_END]);
    }
    
    exit(EXIT_SUCCESS);
}
