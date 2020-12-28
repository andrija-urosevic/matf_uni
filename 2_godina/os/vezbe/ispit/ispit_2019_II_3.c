#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

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

int m, n, k;
float** matrix;

struct thread_info {
    pthread_t thread_id;
    int       start;
};

struct res_info {
    float max_prod;
};

float scalar_product(int row)
{
    float sum = 0;
    for (int i = 0; i < n; i++) {
        sum += matrix[m][i] * matrix[row][i];
    }

    return sum;
}

void* thread_start(void* arg)
{
    struct thread_info* tinfo = (struct thread_info*) arg;
    struct res_info* res = malloc(sizeof (struct res_info));
    check_error(res != NULL, "malloc");

    res->max_prod = scalar_product(tinfo->start);
    for (int i = 1; i < m / k; i++) {
        float tmp_prod = scalar_product(i + tinfo->start);
        if (res->max_prod < tmp_prod) {
            res->max_prod = tmp_prod;
        }
    }

    return res;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 1, "argumenti");

    scanf("%d%d%d", &m, &n, &k);
    matrix = malloc((m + 1) * sizeof (float*));
    check_error(matrix != NULL, "malloc");
    for (int i = 0; i < m + 1; i++) {
        matrix[i] = malloc(n * sizeof (float));
        check_error(matrix[i] != NULL, "malloc");
    }

    for (int i = 0; i < m + 1; i++) {
        for (int j = 0; j < n; j++) {
            scanf("%f", &matrix[i][j]);
        }
    }

    struct thread_info* tinfo  = malloc(k * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < k; i++) {
        tinfo[i].start = i * (m / k);
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                                thread_start, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    struct res_info* res;
    int s = pthread_join(tinfo[0].thread_id, (void*) &res);
    check_thread(s, "pthread_join");
    float max_prod = res->max_prod;
    int max_index = 0;
    free(res);
    for (int i = 1; i < k; i++) {
        int s = pthread_join(tinfo[i].thread_id, (void*) &res);
        check_thread(s, "pthread_join");
        if (max_prod < res->max_prod) {
            max_prod = res->max_prod;
            max_index = i;
        }
        free(res);
    }

    printf("%d %f\n", max_index + 1, max_prod);

    for (int i = 0; i < m + 1; i++) {
        free(matrix[i]);
    }
    free(matrix);
    free(tinfo);
    exit(EXIT_SUCCESS);
}
