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
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

bool should_terminate = false;
bool is_abs = false;
bool is_dub = false;


void hangler(int sig)
{
    switch(sig) {
        case SIGUSR1:
            is_abs = true;
            break;
        case SIGUSR2:
            is_dub = true;
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
    check_error(signal(SIGUSR1, hangler) != SIG_ERR, "signal");
    check_error(signal(SIGUSR2, hangler) != SIG_ERR, "signal");
    check_error(signal(SIGTERM, hangler) != SIG_ERR, "signal");
    
    do {
        pause();
        if (should_terminate) {
            break;
        }

        int num;
        scanf("%d", &num);
        if (is_abs) {
            printf("%d\n", abs(num));
            is_abs = false;
        }
        if (is_dub) {
            printf("%d\n", num * num);
            is_dub = false;
        }
    } while (!should_terminate);

    
    exit(EXIT_SUCCESS);
}
