#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>

int main(int argc, const char *argv[])
{
    mode_t mode = strtol(argv[2], NULL, 8);
    int fd = open(argv[1], O_CREAT, mode);
    printf("%d\n", fd);
    close(fd);

    return 0;
}
