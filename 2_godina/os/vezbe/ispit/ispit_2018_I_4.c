#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

    ssize_t* total_bytes = malloc(nfds * sizeof (ssize_t));
    check_error(total_bytes != NULL, "malloc");
    
    for (int i = 0; i < nfds; i++) {
        int fd = open(argv[i + 1], O_RDONLY | O_NONBLOCK);
        check_error(fd != -1, "open");

        fds[i].fd = fd;
        fds[i].events = POLLIN;
        fds[i].revents = 0;
        
        total_bytes[i] = 0;
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
                ssize_t read_bytes = 0;
                while ((read_bytes = read(fds[i].fd, buf, MAX_SIZE)) > 0) {
                    total_bytes[i] += read_bytes;
                }
                fds[i].revents = 0;
            }

            if (fds[i].revents & (POLLHUP | POLLERR)) {
                close(fds[i].fd);
                fds[i].fd = -1;
                fds[i].events = 0;
                fds[i].revents = 0;
                active_fds--;
            }
        }
    }

    int max_index = 0;
    for (int i = 1; i < nfds; i++) {
        if (total_bytes[max_index] < total_bytes[i]) {
            max_index = i;
        }
    }

    char* filename = strrchr(argv[max_index + 1], '/');
    if (filename == NULL) {
        printf("%s\n", argv[max_index + 1]);
    } else {
        printf("%s\n", filename + 1);
    }
    
    free(total_bytes);
    free(fds);
    exit(EXIT_SUCCESS);
}
