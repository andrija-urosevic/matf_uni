#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
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

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static int    n; 
static int    max_global_index = 0;
static int    max_global_count = 0;

static bool **matrix;

struct thread_info {
    pthread_t thread_id;
    int       index;
};

void* start_thread(void* arg)
{
    struct thread_info* tinfo = (struct thread_info*) arg;

    int count = 0;
    for (int i = 0; i < n; i++) {
        if (matrix[i][tinfo->index]) {
            count++;
        }
    }

    check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
    if (max_global_count < count) {
        max_global_count = count;
        max_global_index = tinfo->index;
    }
    check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");
    
    return NULL;
}

int main(int argc, const char *argv[])
{
    scanf("%d", &n);
    matrix = malloc(n * sizeof (bool*));
    check_error(matrix != NULL, "malloc");
    for (int i = 0; i < n; i++) {
        matrix[i] = malloc(n * sizeof (bool));
        check_error(matrix[i] != NULL, "malloc");
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            scanf("%d", &matrix[i][j]);
        }
    }

    struct thread_info* tinfo = malloc(n * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < n; i++) {
        tinfo[i].index = i;
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                                start_thread, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    for (int i = 0; i < n; i++) {
        int s = pthread_join(tinfo[i].thread_id, NULL);
        check_thread(s, "pthread_join");
    }

    printf("%d\n", max_global_index);

    for (int i = 0; i < n; i++) {
        free(matrix[i]);
    }
    free(matrix);
    free(tinfo);
    exit(EXIT_SUCCESS);
}
