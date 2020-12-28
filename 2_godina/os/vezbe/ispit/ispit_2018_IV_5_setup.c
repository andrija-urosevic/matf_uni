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

void* create_shm_data(const char* pathname, int size) 
{
    int fd = shm_open(pathname, O_RDWR | O_CREAT, 0644);
    check_error(fd != -1, "open");

    check_error(ftruncate(fd, size) != -1, "ftruncate");

    void* addr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    check_error(addr != MAP_FAILED, "mmap");

    close(fd);
    return addr;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    OsInputData* data = create_shm_data(argv[1], sizeof (OsInputData));

    check_error(sem_init(&(data->dataProcessingFinished), 1, 0) != -1, "sem_init");

    scanf("%d", &(data->arrayLen));
    for (int i = 0; i < data->arrayLen; i++) {
        scanf("%d", &(data->array[i]));
    }

    check_error(sem_wait(&(data->dataProcessingFinished)) != -1, "sem_wait");

    for (int i = 0; i < data->arrayLen; i++) {
        printf("%d ", data->array[i]);
    }
    printf("\n");

    check_error(munmap(data, sizeof (OsInputData)) != -1, "munmap");
    return 0;
}
