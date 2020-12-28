#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
#include <pthread.h>
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
    } while(0)

int m, n, k;
float **matrix;

struct thread_info {
    pthread_t thread_id;
    int       start;
};

struct res_info {
    float norm;
};

float norm(int row)
{
    float sum = 0;
    for (int i = 0; i < n; i++) {
        sum += matrix[row][i] * matrix[row][i];
    }

    return sqrt(sum);
}

void* start_thread(void* arg)
{
    struct thread_info* data = (struct thread_info*) arg;
    struct res_info* res = malloc(sizeof (struct res_info));
    check_error(res != NULL, "malloc");

    res->norm = norm(data->start);
    for (int i = 1; i < m / k; i++) {
        float tmp_norm = norm(data->start + i);
        if (res->norm < tmp_norm) {
            res->norm = tmp_norm;
        }
    }

    return res;
}


int main(int argc, const char *argv[])
{
    scanf("%d%d%d", &m, &n, &k);
    matrix = malloc(m * sizeof (float*));
    check_error(matrix != NULL, "malloc");
    for (int i = 0; i < m; i++) {
        matrix[i] = malloc(n * sizeof (float));
        check_error(matrix[i] != NULL, "malloc");
    }

    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            scanf("%f", &matrix[i][j]);
        }
    }

    struct thread_info* tinfo = malloc(m / k * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < k; i++) {
        tinfo[i].start = i * (m / k);
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                                start_thread, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    struct res_info* rinfo;

    int s = pthread_join(tinfo[0].thread_id, (void*) &rinfo);
    check_thread(s, "pthread_join");
    float max_norm = rinfo->norm;
    int max_index = 0;
    free(rinfo);
    for (int i = 1; i < k; i++) {
        int s = pthread_join(tinfo[i].thread_id, (void*) &rinfo);
        check_thread(s, "pthread_join");
        if (max_norm < rinfo->norm ) {
            max_norm = rinfo->norm;
            max_index = i;
        }
        free(rinfo);
    }

    printf("%d %f\n", max_index, max_norm);
       
    for (int i = 0; i < m; i++) {
        free(matrix[i]);
    }
    free(tinfo);
    free(matrix);
    exit(EXIT_SUCCESS);
}
