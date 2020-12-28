#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h> 
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
#include <signal.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int sig1 = 0;
int sig2 = 0;
bool shouldTerminate = false;

void handle(int sig) {
    switch (sig) {
        case SIGUSR1:
            sig1++;
            break;
        case SIGUSR2:
            sig2++;
            break;
        case SIGTERM:
            shouldTerminate = true;
            break;
        default:
            break;
    }
}

int main(void)
{
    check_error(signal(SIGUSR1, handle) != SIG_ERR, "signal");
    check_error(signal(SIGUSR2, handle) != SIG_ERR, "signal");
    check_error(signal(SIGTERM, handle) != SIG_ERR, "signal");

    do {
        pause();
    } while (!shouldTerminate);

    printf("%d %d\n", sig1, sig2);
    
    exit(EXIT_SUCCESS);
}

