#define _XOPEN_SOURCE 700
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

#define RD_END   (0)
#define WR_END   (1)
#define MAX_LEN  (256)
#define MAX_SIZE (1024)

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int fd = open(argv[1], O_RDONLY);
    check_error(fd != -1, "open");

    int fd_err = open("errors.txt", O_WRONLY | O_CREAT | O_TRUNC, 0644);
    check_error(fd_err != -1, "open");

    FILE* f = fdopen(fd, "r");
    check_error(f != NULL, "fdopen");

    char cmd[MAX_LEN];
    char arg[MAX_LEN];
    while (fscanf(f, "%s %s", cmd, arg) == 2) {

        int cld2par[2];
        check_error(pipe(cld2par) != -1, "pipe");

        pid_t pid = fork();
        check_error(pid != -1, "fork");
        if (pid == 0) {
            close(cld2par[RD_END]);

            check_error(dup2(cld2par[WR_END], STDERR_FILENO) != -1, "dup2");

            check_error(execlp(cmd, cmd, arg, NULL) != -1, "execlp");

            close(cld2par[WR_END]);
            exit(EXIT_SUCCESS);
        } else {
            close(cld2par[WR_END]);
            int status;
            check_error(wait(&status) != -1, "wait");

            if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
                ssize_t bytes_read = 0;
                char buf[MAX_SIZE];
                while ((bytes_read = read(cld2par[RD_END], buf, MAX_SIZE)) > 0) {
                    check_error(write(fd_err, buf, bytes_read) != -1, "write");
                }
                check_error(bytes_read != -1, "read");
            }

            close(cld2par[RD_END]);
        }
    }

    fclose(f);
    close(fd_err);
    close(fd);
    exit(EXIT_SUCCESS);
}
