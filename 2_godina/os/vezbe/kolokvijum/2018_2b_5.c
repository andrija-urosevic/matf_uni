#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <ftw.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

const char* ext;

int fn(const char* fpath, const struct stat* sb,
       int typeflag, struct FTW* ftwbuf)
{
    if (typeflag == FTW_F) {
        if (ftwbuf->level >= 2 && ftwbuf->level <= 5) {
            char* file_ext = strrchr(fpath + ftwbuf->base, '.');
            if (file_ext != NULL) {
                if (strcmp(file_ext, ext) == 0) {
                    printf("%s\n", fpath + ftwbuf->base);
                }
            }
        }
    }

    return 0;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    ext = argv[2];

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat");
    check_error(S_ISDIR(sb.st_mode), "not dir");
    check_error(nftw(argv[1], fn, 10, 0) != -1, "nftw");

    exit(EXIT_SUCCESS);
}
