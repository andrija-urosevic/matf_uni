#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
#include <math.h>
#include <pthread.h>

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
    } while (0)

int n, m;
double p;
double** matrix;
double global_sum = 0;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

struct thread_info {
    pthread_t thread_id;
    int       row;   
};

void* start_thread(void* arg)
{
    struct thread_info* data = (struct thread_info*) arg;

    double sum = 0;
    for (int i = 0; i < m; i++) {
        sum += pow(fabs(matrix[data->row][i]), p);
    }

    check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
    global_sum += sum;
    check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");

    return NULL;
}

int main(int argc, const char *argv[])
{
    scanf("%lf%d%d", &p, &n, &m);
    matrix = malloc(n * sizeof (double));
    check_error(matrix != NULL, "malloc");
    for (int i = 0; i < n; i++) {
        matrix[i] = malloc(m * sizeof (double));
        check_error(matrix[i] != NULL, "malloc");
        for (int j = 0; j < m; j++) {
            scanf("%lf", &matrix[i][j]);
        }
    }

    struct thread_info* tinfo = malloc(n * sizeof (struct thread_info));
    check_error(tinfo != NULL, "tinfo");

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

    printf("%lf\n", pow(global_sum, 1/p));
    
    for (int i = 0; i < n; i++) {
        free(matrix[i]);
    }
    free(tinfo);
    free(matrix);
    exit(EXIT_SUCCESS);
}
