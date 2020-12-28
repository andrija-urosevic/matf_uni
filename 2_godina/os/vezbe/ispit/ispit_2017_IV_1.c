#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>

#include <errno.h>
#include <signal.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_SIZE (64)

bool should_terminate = false;
bool should_rot = false;
bool should_upper = false;

void handler(int sig)
{
    switch(sig) {
        case SIGUSR1:
            should_rot = true;
            break;
        case SIGUSR2:
            should_upper = true;
            break;
        case SIGTERM:
            should_terminate = true;
            break;
        default:
            break;
    }
}

void rotate(char* buf)
{
    int i = 0;
    int j = strlen(buf) - 1;
    while (i < j) {
        char tmp = buf[i];
        buf[i] = buf[j];
        buf[j] = tmp;
        i++;
        j--;
    }
}

void upper(char* buf)
{
    for (int i = 0; buf[i]; i++) {
        buf[i] = toupper(buf[i]);
    }
}

int main(int argc, const char *argv[])
{
    check_error(signal(SIGUSR1, handler) != SIG_ERR, "signal");
    check_error(signal(SIGUSR2, handler) != SIG_ERR, "signal");
    check_error(signal(SIGTERM, handler) != SIG_ERR, "signal");

    char buf[MAX_SIZE];
    while (true) {
        pause();
        if (should_terminate) {
            break;
        }
        scanf("%s", buf);
        if (should_rot) {
            rotate(buf);
        } 
        if (should_upper) {
            upper(buf);
        }
        should_rot = false;
        should_upper = false;
        printf("%s\n", buf);
    }
    
    exit(EXIT_SUCCESS);
}
