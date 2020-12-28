#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include <errno.h>
#include <poll.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define MAX_SIZE (1024)

int main(int argc, const char *argv[])
{
    check_error(argc > 1, "argumenti");

    int nfds = argc - 1;
    int active_fds = nfds;

    struct pollfd* fds = malloc(nfds * sizeof (struct pollfd));
    check_error(fds != NULL, "malloc");

    int* max_nums = malloc(nfds * sizeof (int));
    check_error(max_nums != NULL, "malloc");

    FILE** f = malloc(nfds * sizeof (FILE*));
    check_error(f != NULL, "malloc");
    
    for (int i = 0; i < nfds; i++) {
        int fd = open(argv[i + 1], O_RDONLY | O_NONBLOCK);
        check_error(fd != -1, "open");

        f[i] = fdopen(fd, "r");
        check_error(f[i] != NULL, "fdopen");

        fds[i].fd = fd;
        fds[i].events = POLLIN;
        fds[i].revents = 0;
        
        max_nums[i] = INT_MIN;
    }

    char buf[MAX_SIZE];
    while(active_fds) {
        int ret = poll(fds, nfds, -1);
        check_error(ret != -1, "poll");

        if (ret == 0) {
            continue;
        }

        for (int i = 0; i < nfds; i++) {
            if (fds[i].revents & POLLIN) {
                int num;
                while (fscanf(f[i], "%d", &num) == 1) {
                    if (max_nums[i] < num) {
                        max_nums[i] = num;
                    }
                }

                fds[i].revents = 0;
            }

            if (fds[i].revents & (POLLHUP | POLLERR)) {
                close(fds[i].fd);
                fclose(f[i]);
                fds[i].fd = -1;
                fds[i].events = 0;
                fds[i].revents = 0;
                active_fds--;
            }
        }
    }


    int max_index = 0;
    for (int i = 0; i < nfds; i++) {
        if (max_nums[max_index] < max_nums[i]) {
            max_index = i;
        }
    }

    char* filename = strrchr(argv[max_index + 1], '/');
    if (filename == NULL) {
        printf("%d %s\n", max_nums[max_index], argv[max_index + 1]);
    } else {
        printf("%d %s\n", max_nums[max_index], filename + 1);
    }
    
    free(f);
    free(max_nums);
    free(fds);
    exit(EXIT_SUCCESS);
}
