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


int main(int argc, const char *argv[])
{
    char *line = NULL;
    size_t n = 0;
    while (getline(&line, &n, stdin) > 0) {
        char *x = malloc(n * sizeof (char));
        char *y = malloc(n * sizeof (char));
        char *op = malloc(n * sizeof (char));
        sscanf(line, "%s %s %s", x, y, op);

        int cld2par[2];
        check_error(pipe(cld2par) != -1, "pipe");

        pid_t pid = fork();
        check_error(pid != -1, "fork");

        if (pid == 0) {
            close(cld2par[RD_END]);
            check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");
            check_error(execlp("expr", "expr", x, op, y, NULL) != -1, "execlp");
            free(x);
            free(y);
            free(op);
            close(cld2par[WR_END]);
            _exit(EXIT_SUCCESS);
        } else {
            close(cld2par[WR_END]);
            int status;
            check_error(wait(&status) != -1, "wait");

            char *buf = malloc(n * sizeof (char));
            check_error(buf != NULL, "malloc");
            n = read(cld2par[RD_END], buf, n);
            check_error(n != -1, "read");
            check_error(write(STDOUT_FILENO, buf, n) != -1, "write");

            free(buf);
            close(cld2par[RD_END]);
        }
    }

    free(line);
    exit(EXIT_SUCCESS);
}
