#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <errno.h>
#include <semaphore.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define ARRAY_MAX 1024

typedef struct {
    sem_t inDataReady;
    int array[ARRAY_MAX];
    unsigned arrayLen;
} OsData;

void* create_shm_data(const char* pathname, unsigned size)
{
    int fd = shm_open(pathname, O_RDWR | O_CREAT, 0644);
    check_error(fd != -1, "shm_open");

    check_error(ftruncate(fd, size) != -1, "ftruncate");

    void* addr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    check_error(addr != MAP_FAILED, "mmap");

    close(fd);

    return addr;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 3, "argumenti");

    OsData* in = create_shm_data(argv[1], sizeof (OsData));
    OsData* out = create_shm_data(argv[2], sizeof (OsData));

    check_error(sem_init(&(in->inDataReady), 1, 0) != -1, "sem_init");
    check_error(sem_init(&(out->inDataReady), 1, 0) != -1, "sem_init");

    scanf("%u", &(in->arrayLen));
    for (int i = 0; i < in->arrayLen; i++) {
        scanf("%d", &(in->array[i]));
    }

    check_error(sem_post(&(in->inDataReady)) != -1, "sem_post");

    check_error(sem_wait(&(out->inDataReady)) != -1, "sem_wait");

    for (int i = 0; i < out->arrayLen; i++) {
        printf("%d ", out->array[i]);
    }
    printf("\n");

    check_error(munmap(in, sizeof (OsData)) != -1, "munmap");
    check_error(munmap(out, sizeof (OsData)) != -1, "munmap");
    
    exit(EXIT_SUCCESS);
}
