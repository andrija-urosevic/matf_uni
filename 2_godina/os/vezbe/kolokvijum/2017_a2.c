#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <pwd.h>
#include <grp.h>

#include <stdio.h>
#include <stdlib.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

void user_group(const char* pathname)
{
    struct stat sb;
    check_error(lstat(pathname, &sb) != -1, "lstat");

    struct passwd* usr = getpwuid(sb.st_uid);
    struct group* grp = getgrgid(sb.st_gid); 

    printf("%s %s\n", usr->pw_name, grp->gr_name);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    user_group(argv[1]);

    exit(EXIT_SUCCESS);
}
