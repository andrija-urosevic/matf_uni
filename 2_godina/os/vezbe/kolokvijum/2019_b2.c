#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <pwd.h>
#include <grp.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int vlaskink_grupa(const char *pathname)
{
    struct stat sb;
    check_error(lstat(pathname, &sb) != -1, "stat");
    check_error(S_ISLNK(sb.st_mode), "nije link");

    uid_t uid_lnk = sb.st_uid;
    gid_t gid_lnk = sb.st_gid;

    check_error(stat(pathname, &sb) != -1, "stat");

    uid_t uid_reg = sb.st_uid;
    gid_t gid_reg = sb.st_gid;

    return uid_lnk == uid_reg &&
           gid_lnk == gid_reg;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    if (vlaskink_grupa(argv[1])) {
        printf("da\n");
    } else {
        printf("ne\n");
    }

    exit(EXIT_SUCCESS);
}
