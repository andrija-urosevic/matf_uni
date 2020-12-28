#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
#include <pthread.h>
#include <limits.h>
#include <math.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define check_thread(err_thread, user_msg) \
    do { \
        int _err_thread = (err_thread); \
        if (_err_thread > 0) { \
            errno = _err_thread; \
            check_error(false, user_msg); \
        } \
    } while(0);

#define STEP (2)

typedef struct point {
    double x;
    double y;
}point_t;

int n = 0;
point_t* points;
double min_global_distance;
bool is_init = false;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

struct thread_info {
    pthread_t thread_id;
    int point_index;
};

void* start_thread(void* arg)
{
    struct thread_info* data = (struct thread_info*) arg;

    double min_distance = INT_MAX;
    for (int i = 0; i < n; i++) {
        if (data->point_index != i) {
            double dx = points[i].x - points[data->point_index].x;
            double dy = points[i].y - points[data->point_index].y;
            double distance = dx*dx + dy*dy;
            if (min_distance > distance) {
                min_distance = distance;
            }
        }
    }

    check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
    if (is_init) {
        if (min_global_distance > min_distance) {
            min_global_distance = min_distance;
        }
    } else {
        is_init = true;
        min_global_distance = min_distance;
    }
    
    check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");

    return NULL;
}

int main(int argc, const char *argv[])
{
    int aloc = 10;
    struct thread_info* tinfo = malloc(aloc * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    points = malloc(aloc * sizeof (point_t));
    check_error(points != NULL, "malloc");

    double x, y;
    while (scanf("%lf %lf", &x, &y) == 2) {
        if (aloc <= n) {
            aloc *= STEP;

            tinfo = realloc(tinfo, aloc * sizeof (struct thread_info));
            check_error(tinfo != NULL, "realloc");

            points = realloc(points, aloc * sizeof (point_t));
            check_error(points != NULL, "realloc");
        }
        points[n].x = x;
        points[n].y = y;

        tinfo[n].point_index = n;
        n++;
    }

    for (int i = 0; i < n; i++) {
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                               start_thread, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    for (int i = 0; i < n; i++) {
        int s = pthread_join(tinfo[i].thread_id, NULL);
        check_thread(s, "pthread_join");
    }

    printf("%lf\n", sqrt(min_global_distance));
    
    free(points);
    free(tinfo);
    exit(EXIT_SUCCESS);
}
