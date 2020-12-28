#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <signal.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

bool should_terminate = false;
int score = 0;

void handler(int sig) 
{
    switch (sig) {
        case SIGUSR1:
            score += 1;
            break;
        case SIGUSR2:
            score += 2;
            break;
        case SIGINT:
            score -= 4;
            break;
        case SIGTERM:
            should_terminate = true;
            break;
        default:
            break;
    }
}

int main(int argc, const char *argv[])
{
    check_error(signal(SIGUSR1, handler) != SIG_ERR, "signal");
    check_error(signal(SIGUSR2, handler) != SIG_ERR, "signal");
    check_error(signal(SIGINT, handler) != SIG_ERR, "signal");
    check_error(signal(SIGTERM, handler) != SIG_ERR, "signal");

    do {
        pause();
    } while (!should_terminate);

    printf("%d\n", score);
    
    exit(EXIT_SUCCESS);
}
