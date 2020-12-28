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
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define RD_END (0)
#define WR_END (1)
#define MAX_SIZE (1024)

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int cld2par[2];
    check_error(pipe(cld2par) != -1, "pipe");


    pid_t pid = fork();
    check_error(pid != -1, "fork");

    int size = 0;
    if (pid == 0) {
        close(cld2par[RD_END]);

        check_error(dup2(cld2par[WR_END], STDOUT_FILENO) != -1, "dup2");

        check_error(execlp("stat", "stat", "--format=%s", argv[1], NULL) != -1, "execlp");
    } else {
        close(cld2par[WR_END]);

        char buffer[MAX_SIZE];
        int bytes_read = read(cld2par[RD_END], buffer, MAX_SIZE);
        check_error(bytes_read != -1, "read");

        buffer[bytes_read] = '\0';
        size = atoi(buffer);
    }

    int status;
    check_error(wait(&status) != -1, "wait");
    if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
        printf("Neuspeh\n");
        exit(EXIT_SUCCESS);
    }

    printf("%d\n", size);
    
    exit(EXIT_SUCCESS);
}
