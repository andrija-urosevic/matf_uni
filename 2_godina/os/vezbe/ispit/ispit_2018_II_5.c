#define _GNU_SOURCE
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

typedef struct {
    sem_t inDataReady;
    sem_t dataProcessed;
    char str[ARRAY_MAX];
}OsInputData;

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

int main(int argc, const char *argv[])
{
    check_error(argc == 2, "argumenti");

    int size = 0;
    OsInputData* data = get_shm_data(argv[1], &size);

    check_error(sem_wait(&(data->inDataReady)) != -1, "sem_wait");

    printf("Data: %s\n", data->str);
    int i = 0;
    int j = strlen(data->str) - 1;

    while (i < j) {
        char tmp = data->str[i];
        data->str[i] = data->str[j];
        data->str[j] = tmp;
        i++;
        j--;
    }

    check_error(sem_post(&(data->dataProcessed)) != -1, "sem_post");

    check_error(munmap(data, size) != -1, "munmap");
    return 0;
}
