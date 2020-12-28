#define _GNU_SOURCE
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include <signal.h>
#include <semaphore.h>
#include <errno.h>
#include <ctype.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define ARRAY_MAX 1024

static bool is_neg = false;
static bool is_dup = false;

typedef struct {
    sem_t dataProcessingFinished;
    int array[ARRAY_MAX];
    unsigned arrayLen;
} OsInputData;

void* get_shm_data(const char* pathname, int* size) 
{
    int fd = shm_open(pathname, O_RDWR, 0644);
    check_error(fd != -1, "open");

    struct stat sb;
    check_error(fstat(fd, &sb) != -1, "fstat");
    *size = sb.st_size;

    void* addr = mmap(NULL, *size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    check_error(addr != MAP_FAILED, "mmap");

    close(fd);
    return addr;
}

void handler(int sig)
{
    switch(sig) {
        case SIGUSR1:
            is_neg = true;
            break;
        case SIGUSR2:
            is_dup = true;
            break;
    }
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int size = 0;
    OsInputData* data = get_shm_data(argv[1], &size);
    check_error(signal(SIGUSR1, handler) != SIG_ERR, "signal");
    check_error(signal(SIGUSR2, handler) != SIG_ERR, "signal");

    pause();
    if (is_neg) {
        for (int i = 0; i < data->arrayLen; i++) {
            data->array[i] *= -1;
        }
    }
    if (is_dup) {
        for (int i = 0; i < data->arrayLen; i++) {
            data->array[i] *= 2;
        }
    }

    check_error(sem_post(&(data->dataProcessingFinished)) != -1, "sem_wait");

    check_error(munmap(data, size) != -1, "munmap");
    return 0;
}
