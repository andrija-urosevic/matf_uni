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

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define check_thread(thread_err, user_msg) \
    do { \
        int _thread_err = (thread_err); \
        if (_thread_err > 0) { \
            errno = _thread_err; \
            check_error(false, user_msg); \
        } \
    } while(0)

int n, m;
double** matrix;
double global_min = INT_MAX;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

struct thread_info {
    pthread_t thread_id;
    int       row;
};


void* start_thread(void* arg)
{
    struct thread_info* data = (struct thread_info*) arg;

    double min = matrix[data->row][0];
    for (int i = 1; i < m; i++) {
        if (min > matrix[data->row][i]) {
            min = matrix[data->row][i];
        }
    }

    check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
    if (global_min > min) {
        global_min = min;
    }
    check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");

    return NULL;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    FILE* f = fopen(argv[1], "r");
    check_error(f != NULL, "fopen");

    fscanf(f, "%d%d", &n, &m);
    matrix = malloc(n * sizeof (double*));
    for (int i = 0; i < n; i++) {
        matrix[i] = malloc(m * sizeof (double));
        check_error(matrix[i] != NULL, "malloc");
        for (int j = 0; j < m; j++) {
            fscanf(f, "%lf", &matrix[i][j]);
        }
    }

    struct thread_info* tinfo = malloc(n * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < n; i++) {
        tinfo[i].row = i;
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                               start_thread, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    for (int i = 0; i < n; i++) {
        int s = pthread_join(tinfo[i].thread_id, NULL);
        check_thread(s, "pthread_join");
    }

    printf("%lf\n", global_min);

    for (int i = 0; i < n; i++) {
        free(matrix[i]);
    }
    free(matrix);
    free(tinfo);
    fclose(f);
    exit(EXIT_SUCCESS);
}
