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
#define MAX_LEN (1024)

int main(int argc, const char *argv[])
{
    check_error(argc > 1, "argumenti");

    for (int i = 1; i < argc; i++) {
        int cld2par[2];
        check_error(pipe(cld2par) != -1, "pipe");

        pid_t pid = fork();
        check_error(pid != -1, "fork");
        if (pid == 0) {
            close(cld2par[RD_END]);

            check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");

            check_error(execlp("du", "du", "-sch", argv[i], NULL) != -1, "execlp");

            close(cld2par[WR_END]);
            _exit(EXIT_SUCCESS);
        } else {
            close(cld2par[WR_END]);

            int status;
            check_error(wait(&status) != -1, "wait");
            if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
                printf("neuspeh ");
                close(cld2par[RD_END]);
                continue;
            }
            
            char buf[MAX_LEN];
            check_error(read(cld2par[RD_END], buf, MAX_LEN) != -1, "read");
            char to_print[MAX_LEN];
            sscanf(buf, "%s", to_print);
            printf("%s ", to_print);

            close(cld2par[RD_END]);
        }
    }
    
    exit(EXIT_SUCCESS);
}
