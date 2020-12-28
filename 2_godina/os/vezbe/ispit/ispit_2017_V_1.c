#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

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

#define MAX_SIZE (2048)

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static int global_stop_index[MAX_SIZE];
static int global_stop_size = 0;

static int offset;

struct thread_info {
    pthread_t   thread_id;
    const char *filename;
    int         index;
};

void* thread_start(void* arg)
{
    struct thread_info* tinfo = (struct thread_info*) arg;

    FILE* f = fopen(tinfo->filename, "r");
    check_error(f != NULL, "fopen");

    char* genom = malloc((offset + 1) * sizeof (char));
    check_error(genom != NULL, "malloc");

    fseek(f, tinfo->index * offset, SEEK_SET);
    fgets(genom, offset + 1, f);
    fclose(f);

    for (int i = 0; genom[i + 2] != 0 && genom[i + 2] != '\n'; i++) {
        if (strncmp(genom + i, "tag", 3) != 0 &&
            strncmp(genom + i, "taa", 3) != 0 &&
            strncmp(genom + i, "tga", 3) != 0) {
            continue;
        }

        check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
        global_stop_index[global_stop_size] = 
            tinfo->index * offset + i;
        global_stop_size++;
        check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");
    }

    return NULL;
}


int main(int argc, const char *argv[])
{
    check_error(argc == 3, "argumenti");
    int num_threads = atoi(argv[1]);

    struct stat sb;
    check_error(lstat(argv[2], &sb) != -1, "lstat");
    offset = sb.st_size / num_threads;

    struct thread_info* tinfo = 
        malloc(num_threads * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < num_threads; i++) {
        tinfo[i].filename = argv[2];
        tinfo[i].index = i;

        int s = pthread_create(&tinfo[i].thread_id, NULL,
                                thread_start, &tinfo[i]);
        check_thread(s, "pthread_create");
    }


    for (int i = 0; i < num_threads; i++) {
        int s = pthread_join(tinfo[i].thread_id, NULL);
        check_thread(s, "pthread_join");
    }

    for (int i = 0; i < global_stop_size; i++) {
        printf("%d ", global_stop_index[i]);
    }
    printf("\n");
    
    free(tinfo);
    exit(EXIT_SUCCESS);
}
