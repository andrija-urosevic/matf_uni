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
    } while(0)

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static int** A;
static int** B;
static int** AB;

static int n;
static int m;
static int k;

static int max;

struct thread_info {
    pthread_t thread_id;
    int       i;
    int       j;
};

void* thread_start(void* arg)
{
    struct thread_info* tinfo = (struct thread_info*) arg;

    int sum = 0;
    for (int l = 0; l < m; l++) {
        sum += A[tinfo->i][l] * B[l][tinfo->j];
    }

    check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
    AB[tinfo->i][tinfo->j] = sum;
    if (max < sum) {
        max = sum;
    }
    check_thread(pthread_mutex_unlock(&mutex), "pthread_unmutex_lock");

    return NULL;
}


int main(int argc, const char *argv[])
{
    scanf("%d%d", &n, &m);
    A = malloc(n * sizeof (int*));
    check_error(A != NULL, "malloc");
    for (int i = 0; i < n; i++) {
        A[i] = malloc(m * sizeof (int));
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < m; j++) {
            scanf("%d", &A[i][j]);
        }
    }
    scanf("%d%d", &m, &k);
    B = malloc(m * sizeof (int*));
    check_error(B != NULL, "malloc");
    for (int i = 0; i < m; i++) {
        B[i] = malloc(k * sizeof (int));
    }

    for (int i = 0; i < m; i++) {
        for (int j = 0; j < k; j++) {
            scanf("%d", &B[i][j]);
        }
    }

    AB = malloc(n * sizeof (int*));
    check_error(AB != NULL, "malloc");
    for (int i = 0; i < n; i++) {
        AB[i] = malloc(k * sizeof(int));
    }

    struct thread_info** tinfo = malloc(n * sizeof (struct thread_info*));
    check_error(tinfo != NULL, "malloc");
    for (int i = 0; i < n; i++) {
        tinfo[i] = malloc(k * sizeof (struct thread_info));
        check_error(tinfo[i] != NULL, "malloc");
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < k; j++) {
            AB[i][j] = 0;

            tinfo[i][j].i = i;
            tinfo[i][j].j = j;
            int s = pthread_create(&tinfo[i][j].thread_id, NULL, 
                                    thread_start, &tinfo[i][j]);
            check_thread(s, "pthread_create");
        }
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < k; j++) {
            int s = pthread_join(tinfo[i][j].thread_id, NULL);
            check_thread(s, "pthread_join");
        }
        free(tinfo[i]);
    }
    free(tinfo);

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < k; j++) {
            printf("%d ", AB[i][j]);
        }
        printf("\n");
    }
    printf("%d\n", max);
    
    for (int i = 0; i < n; i++) {
        free(AB[i]);
    }
    for (int i = 0; i < m; i++) {
        free(B[i]);
    }
    for (int i = 0; i < n; i++) {
        free(A[i]);
    }
    free(AB);
    free(B);
    free(A);
    exit(EXIT_SUCCESS);
}
