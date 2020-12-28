#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <ftw.h>

#include <stdio.h>
#include <stdlib.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int num_reg = 0;
int num_dir = 0;
int num_chr = 0;
int num_blk = 0;
int num_lnk = 0;
int num_ifo = 0;
int num_sck = 0;

int fn(const char *fpath, const struct stat *sb,
           int typeflag, struct FTW *ftwbuf)
{
    switch (sb->st_mode & S_IFMT) {
        case S_IFREG:  num_reg++; break;
        case S_IFDIR:  num_dir++; break;
        case S_IFCHR:  num_chr++; break;
        case S_IFBLK:  num_blk++; break;
        case S_IFLNK:  num_lnk++; break;
        case S_IFIFO:  num_ifo++; break;
        case S_IFSOCK: num_sck++; break;
    }

    return 0;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(lstat(argv[1], &sb) != -1, "lstat");
    check_error(S_ISDIR(sb.st_mode), "nije dir");

    check_error(nftw(argv[1], fn, 50, FTW_PHYS) == 0, "nftw");

    printf("%d %d %d %d %d %d %d %d\n", num_reg, num_dir, num_chr, num_blk,
                                        num_lnk, num_ifo, num_sck,
                                        num_reg + num_dir + num_chr +
                                        num_blk + num_lnk + num_ifo + 
                                        num_sck);

    exit(EXIT_SUCCESS);
}
