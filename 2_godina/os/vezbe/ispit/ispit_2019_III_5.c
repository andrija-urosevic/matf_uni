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

void* get_shm_data(const char* pathname, unsigned* size)
{
    int fd = shm_open(pathname, O_RDWR, 0644);
    check_error(fd != -1, "shm_open");

    struct stat sb;
    check_error(fstat(fd, &sb) != -1, "fstat");
    *size = sb.st_size;

    void* addr = mmap(NULL, *size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    check_error(addr != MAP_FAILED, "mmap");

    close(fd);

    return addr;
}

bool has_ones(int num) 
{
    int count = 0;
    unsigned mask = 1;
    while (mask) {
        if (mask & num) {
            count++;
        }
        mask <<= 1;
    }

    return count >= 4;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 3, "argumenti");

    unsigned size_in = 0;
    unsigned size_out = 0;
    OsData* in = get_shm_data(argv[1], &size_in);
    OsData* out = get_shm_data(argv[2], &size_out);

    check_error(sem_wait(&(in->inDataReady)) != -1, "sem_wait");
    out->arrayLen = 0;
    for (int i = 0; i < in->arrayLen; i++) {
        if (has_ones(in->array[i])) {
            out->array[out->arrayLen] = in->array[i];
            out->arrayLen++;
        }
    }
    check_error(sem_post(&(out->inDataReady)) != -1, "sem_post");

    check_error(munmap(in, size_in) != -1, "munmap");
    check_error(munmap(out, size_out) != -1, "munmap");
    
    exit(EXIT_SUCCESS);
}
