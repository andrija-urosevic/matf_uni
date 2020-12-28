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

    struct passwd* user = getpwuid(sb.st_uid);
    check_error(user != NULL, "getpwuid");

    struct group* group = getgrgid(sb.st_gid);
    check_error(group != NULL, "getgrgid");

    return strcmp(user->pw_name, group->gr_name) == 0;
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
