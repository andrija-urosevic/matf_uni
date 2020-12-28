#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

bool is_public(const char* pathname)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");
    check_error(S_ISREG(sb.st_mode), "nije reg");

    return (sb.st_mode & S_IROTH) && (sb.st_mode & S_IWOTH);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    if (is_public(argv[1])) {
        printf("true\n");
    } else {
        printf("false\n");
    }

    exit(EXIT_SUCCESS);
}
