#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/epoll.h>
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

#define MAX_EVENTS 10

typedef struct {
    int   fd;
    int   ind;
}epoll_data;

int main(int argc, const char *argv[])
{
    check_error(argc > 1, "argumenti");

    int nfds = argc - 1;

    FILE** streams = malloc(nfds * sizeof (FILE*));
    check_error(streams != NULL, "malloc");

    double* sum = malloc(nfds * sizeof (double));
    check_error(sum != NULL, "malloc");

    int epollfd = epoll_create(nfds);
    check_error(epollfd != -1, "epoll_create");

    struct epoll_event ev;
    for (int i = 0; i < nfds; i++) {
        int fd = open(argv[i + 1], O_RDONLY | O_NONBLOCK);
        check_error(fd != -1, "open");

        streams[i] = fdopen(fd, "r");
        check_error(streams[i] != NULL, "fdopen");

        epoll_data* epolldata = malloc(sizeof (epoll_data));
        check_error(epolldata != NULL, "malloc");

        sum[i] = 0;

        epolldata->fd = fd;
        epolldata->ind = i;

        ev.events = EPOLLIN;
        ev.data.ptr = epolldata;
        check_error(epoll_ctl(epollfd, EPOLL_CTL_ADD, fd, &ev) != -1, "epoll_ctl");
    }

    struct epoll_event events[MAX_EVENTS];

    int num_active = nfds;
    while (num_active > 0) {
        int ready = epoll_wait(epollfd, events, MAX_EVENTS, -1);
        check_error(ready != -1, "epoll_wait");

        for (int i = 0; i < ready; i++) {
            epoll_data* data = (epoll_data*) events[i].data.ptr;
            if (events[i].events & EPOLLIN) {
                double num;
                while (fscanf(streams[data->ind], "%lf", &num) == 1) {
                    sum[data->ind] += num;
                }
            }
            if (events[i].events & (EPOLLHUP | EPOLLERR)) {
                close(data->fd);
                free(data);
                num_active--;
            }
        }
    }

    int max_index = 0;
    for (int i = 1; i < nfds; i++) {
        if (sum[max_index] < sum[i]) {
            max_index = i;
        }
    }

    printf("%s\n", argv[max_index + 1]);

    for (int i = 0; i < nfds; i++) {
        fclose(streams[i]);
    }
    
    free(sum);
    free(streams);
    close(epollfd);
    exit(EXIT_SUCCESS);
}
