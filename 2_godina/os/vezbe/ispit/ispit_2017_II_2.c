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
#define MAX_LEN (11)

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");
    int cld2par[2];
    check_error(pipe(cld2par) != -1, "pipe");

    pid_t pid = fork();
    check_error(pid != -1, "fork");

    if (pid == 0) {
        close(cld2par[RD_END]);

        check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");

        check_error(execlp("ls", "ls", "-l", argv[1], NULL) != -1, "execlp");

        _exit(EXIT_SUCCESS);
        close(cld2par[WR_END]);
    } else {
        close(cld2par[WR_END]);
        int status;
        check_error(wait(&status) != -1, "wait");
        if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
            printf("Neuspeh\n");
            exit(EXIT_SUCCESS);
        }

        char buf[MAX_LEN];
        ssize_t bytes_read = read(cld2par[RD_END], buf, MAX_LEN);
        check_error(bytes_read != -1, "read");
        buf[bytes_read] = 0;
        printf("%s\n", buf);

        close(cld2par[RD_END]);
    }
    
    exit(EXIT_SUCCESS);
}
