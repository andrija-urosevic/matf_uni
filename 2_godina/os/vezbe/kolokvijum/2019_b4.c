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

void promeni_dozvole(const char* pathname1, const char* pathname2)
{
    struct stat sb;

    check_error(stat(pathname1, &sb) != -1, "stat");
    mode_t mode1 = sb.st_mode;
    check_error(stat(pathname1, &sb) != -1, "stat");
    mode_t mode2 = sb.st_mode & ~(S_IRWXU | S_IRWXG | S_IRWXO);

    mode_t mode1_usr = (mode1 & S_IRWXU) >> 6;
    mode_t mode1_grp_oth = (mode1 & (S_IRWXG | S_IRWXO)) << 3;

    mode2 |= mode1_usr | mode1_grp_oth;

    check_error(chmod(pathname2, mode2) != -1, "chmod");
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    promeni_dozvole(argv[1], argv[2]);

    exit(EXIT_SUCCESS);
}
