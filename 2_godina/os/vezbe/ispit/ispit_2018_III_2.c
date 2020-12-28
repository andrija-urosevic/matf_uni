#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
#include <pthread.h>
#include <ctype.h>

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

#define NUM_LETTERS 26

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static int global_max = 0;
static int letters[NUM_LETTERS];

struct thread_info {
    pthread_t   thread_id;
    int         index;
    const char* filename;
};

void* thread_start(void* arg)
{
    struct thread_info* tinfo = (struct thread_info*) arg;

    FILE* f = fopen(tinfo->filename, "r");
    check_error(f != NULL, "fopen");

    char c;
    int count = 0;
    while (fscanf(f, "%c", &c) == 1) {
        if ('a' + tinfo->index == tolower(c)) {
            count++;
        }
    }

    fclose(f);

    check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
    letters[tinfo->index] = count;
    if (letters[global_max] < letters[tinfo->index]) {
        global_max = tinfo->index;
    }
    check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");

    return NULL;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    struct thread_info* tinfo = malloc(NUM_LETTERS * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < NUM_LETTERS; i++) {
        letters[i] = 0;
        tinfo[i].index = i;
        tinfo[i].filename = argv[1];
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                                thread_start, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    for (int i = 0; i < NUM_LETTERS; i++) {
        check_thread(pthread_join(tinfo[i].thread_id, NULL), "pthread_join");
    }

    for (int i = 0; i < NUM_LETTERS; i++) {
        printf("%d ", letters[i]);
    }

    printf("\n%c\n", 'a' + global_max);

    free(tinfo);
    exit(EXIT_SUCCESS);
}
