#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void ispis_dozvola(const char* pathname)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");

    char permitions[] = "-rwxrwxrwx";

    if (S_ISDIR(sb.st_mode)) {
        permitions[0] = 'd';
    }

    if (!(sb.st_mode & S_IRUSR)) {
        permitions[1] = '-';
    }
    if (!(sb.st_mode & S_IWUSR)) {
        permitions[2] = '-';
    }
    if (!(sb.st_mode & S_IXUSR)) {
        permitions[3] = '-';
    }

    if (!(sb.st_mode & S_IRGRP)) {
        permitions[4] = '-';
    }
    if (!(sb.st_mode & S_IWGRP)) {
        permitions[5] = '-';
    }
    if (!(sb.st_mode & S_IXGRP)) {
        permitions[6] = '-';
    }


    if (!(sb.st_mode & S_IROTH)) {
        permitions[7] = '-';
    }
    if (!(sb.st_mode & S_IWOTH)) {
        permitions[8] = '-';
    }
    if (!(sb.st_mode & S_IXOTH)) {
        permitions[9] = '-';
    }

    printf("%s\n", permitions);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    ispis_dozvola(argv[1]);

    exit(EXIT_SUCCESS);
}
