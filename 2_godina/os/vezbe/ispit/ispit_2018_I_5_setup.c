#define _XOPEN_SOURCE (700)
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>

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
    sem_t dataProcessed;
    char str[ARRAY_MAX];
}OsInputData;


void* create_shm_block(const char* pathname, int size) 
{
    int fd = shm_open(pathname, O_RDWR | O_CREAT, 0644);
    check_error(fd != -1, "shm_open");

    check_error(ftruncate(fd, size) != -1, "ftruncate");

    void* addr = mmap(0, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    check_error(addr != MAP_FAILED, "mmap");

    close(fd);

    return addr;
}

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    OsInputData* data = create_shm_block(argv[1], sizeof (OsInputData));
    check_error(sem_init(&(data->inDataReady), 1, 0) != -1, "sem_init");
    check_error(sem_init(&(data->dataProcessed), 1, 0) != -1, "sem_init");

    scanf("%s", data->str);

    check_error(sem_post(&(data->inDataReady)) != -1, "sem_post");

    check_error(sem_wait(&(data->dataProcessed)) != -1, "sem_wait");

    printf("%s\n", data->str);
   
    check_error(munmap(data, sizeof (OsInputData)) != -1, "munmap");
    exit(EXIT_SUCCESS);
}
