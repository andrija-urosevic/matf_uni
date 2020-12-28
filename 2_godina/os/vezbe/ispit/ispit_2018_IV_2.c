#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>

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
    check_error(argc > 1, "argumenti");

    char** args = malloc(argc * sizeof (char*)); 
    for (int i = 0; i < argc - 1; i++) {
        args[i] = argv[i + 1];
    }
    args[argc - 1] = NULL;

    int cld2par[2];
    check_error(pipe(cld2par) != -1, "pipe");

    int count = 0;
    
    pid_t pid = fork();
    check_error(pid != -1, "fork");

    if (pid == 0) {
        close(cld2par[RD_END]);

        check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");
        check_error(execvp(argv[1], args) != -1, "execvp");

        close(cld2par[WR_END]);
        _exit(EXIT_SUCCESS);
    } else {
        close(cld2par[WR_END]);
        int status;
        check_error(wait(&status) != -1, "wait");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
            printf("Neuspeh\n");
            exit(EXIT_FAILURE);
        }

        FILE* f = fdopen(cld2par[RD_END], "r");
        check_error(f != NULL, "fdopen");

        char* line = NULL;
        size_t n = 0;
        while (getline(&line, &n, f) != -1) {
            count++;
        }

        fclose(f);
        close(cld2par[RD_END]);
    }

    printf("%d\n", count);
    
    exit(EXIT_SUCCESS);
}
