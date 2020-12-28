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
    } while (0)

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static const char* pathname;
static const char* word;

static int global_count = 0;
static int offset;

struct thread_info {
    pthread_t thread_id;
    int       index;
};

void* thread_start(void* arg)
{
    struct thread_info* tinfo = (struct thread_info*) arg;
    int fd = open(pathname, O_RDONLY);

    char* line = malloc((offset + 1) * sizeof (char));
    lseek(fd, tinfo->index * offset, SEEK_SET);

    ssize_t nbytes = read(fd, line, offset + 1);
    check_error(nbytes != -1, "read");
    line[nbytes] = 0;

    int len = strlen(word);
    for (int i = 0; line[i + len]; i++) {
        if (strncmp(line + i, word, len) != 0) {
            continue;
        }
        check_thread(pthread_mutex_lock(&mutex), "pthread_mutex_lock");
        global_count++;
        check_thread(pthread_mutex_unlock(&mutex), "pthread_mutex_unlock");
    }
    free(line);

    close(fd);
}


int main(int argc, const char *argv[])
{
    check_error(argc == 4, "argumenti");

    pathname = argv[1];
    word = argv[2];
    int k = atoi(argv[3]);

    struct stat sb;
    check_error(lstat(pathname, &sb) != -1, "lstat");
    offset = sb.st_size / k;

    struct thread_info* tinfo = malloc(k * sizeof (struct thread_info));
    check_error(tinfo != NULL, "malloc");

    for (int i = 0; i < k; i++) {
        tinfo[i].index = i;
        int s = pthread_create(&tinfo[i].thread_id, NULL, 
                                thread_start, &tinfo[i]);
        check_thread(s, "pthread_create");
    }

    for (int i = 0; i < k; i++) {
        int s = pthread_join(tinfo[i].thread_id, NULL);
        check_thread(s, "pthread_join");
    }

    printf("%d\n", global_count);
    
    free(tinfo);
    exit(EXIT_SUCCESS);
}
