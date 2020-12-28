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
            perror(usermsg); \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void zameni(const char* pathname)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");

    mode_t new_mode = (sb.st_mode >> 9) << 9;

    mode_t usr = sb.st_mode & S_IRWXU;
    mode_t grp_oth = sb.st_mode & (S_IRWXG | S_IRWXO);

    new_mode |= usr >> 6;
    new_mode |= grp_oth << 3;

    check_error(chmod(pathname, new_mode) != -1, "chmod");
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    zameni(argv[1]);

    exit(EXIT_SUCCESS);
}
