#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>

#include <errno.h>
#include <semaphore.h>
#include <math.h>

#define check_error(expr, user_msg) \
    do { \
        if (!(expr)) { \
            perror(user_msg); \
            exit(EXIT_FAILURE); \
        } \
    } while(0)

#define ARRAY_MAX (1024)

typedef struct {
    sem_t inDataReady;
    float array[ARRAY_MAX];
    unsigned arrayLen;
}OsInputData;

void* get_shm_block(const char* pathname, int* size)
{
    int fd = shm_open(pathname, O_RDWR, 0644);
    check_error(fd != -1, "shm_open");

    struct stat sb;
    check_error(fstat(fd, &sb) != -1, "fstat");
    *size = sb.st_size;

    void* addr = mmap(0, *size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    check_error(addr != MAP_FAILED, "mmap");

    close(fd);

    return addr;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int size = 0;
    OsInputData* data = get_shm_block(argv[1], &size);
    
    check_error(sem_wait(&(data->inDataReady)) != -1, "sem_wait");

    float mu = 0;
    for (int i = 0; i < data->arrayLen; i++) {
        mu += data->array[i];
    }
    mu /= (float) data->arrayLen;

    float sigma = 0;
    for (int i = 0; i < data->arrayLen; i++) {
        sigma += (data->array[i] - mu) * (data->array[i] - mu);
    }

    sigma /= (float) data->arrayLen;

    printf("%f\n", sqrt(sigma));

    check_error(munmap(data, size) != -1, "munmap");
    exit(EXIT_SUCCESS);
}
