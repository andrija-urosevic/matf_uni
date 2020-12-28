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

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat"); 
    
    mode_t oth_mode = sb.st_mode % 8;
    mode_t grp_mode = (sb.st_mode / 8) % 8;

    mode_t new_mode =  sb.st_mode / 64;
    new_mode *= 8;
    new_mode += oth_mode;
    new_mode *= 8;
    new_mode += grp_mode;

    check_error(chmod(argv[1], new_mode) != -1, "chmod");

    exit(EXIT_SUCCESS);
}
