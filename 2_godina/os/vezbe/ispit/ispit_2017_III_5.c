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

#define ARRAY_MAX (1024)

typedef struct {
    sem_t inDataReady;
    int array[ARRAY_MAX];
    unsigned arrayLen;
}OsInputData;

bool has_ones(int num)
{
    int count = 0;
    int mask = 1;
    while (mask) {
        if (num & mask) {
            count++;
        }
        mask <<= 1;
    }

    return count >= 4;
}

void* get_shm_data(const char* pathname, int* size)
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
    int size = 0;
    OsInputData* data = get_shm_data(argv[1], &size);
    
    check_error(sem_wait(&(data->inDataReady)) != -1, "sem_wait");

    for (int i = 0; i < data->arrayLen; i++) {
        if (has_ones(data->array[i])) {
            printf("%d ", data->array[i]);
        }
    }

    check_error(munmap(data, size) != -1, "munmap");
    exit(EXIT_SUCCESS);
}
