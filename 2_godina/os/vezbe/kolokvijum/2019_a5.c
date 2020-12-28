#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <ftw.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int fn(const char *fpath, const struct stat *sb,
       int typeflag, struct FTW *ftwbuf);

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat");
    check_error(S_ISDIR(sb.st_mode), "not dir");

    nftw(argv[1], fn, 50, FTW_PHYS);

    exit(EXIT_SUCCESS);
}

int fn(const char *fpath, const struct stat *sb,
       int typeflag, struct FTW *ftwbuf)
{
    if (typeflag == FTW_D) {
        if (ftwbuf->level >= 1 && ftwbuf->level <= 3) {
            if (strchr(fpath + ftwbuf->base, '.') != NULL) {
                printf("%s\n", fpath + ftwbuf->base);
            }
        }
    }

    return 0;
}
