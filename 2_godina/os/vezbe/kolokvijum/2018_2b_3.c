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

int change_permition(const char* pathname, const char* change)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");
    mode_t new_mode = sb.st_mode;

    mode_t mask = 0;
    if (change[2] == 'r') {
        mask |= S_IROTH;
    } else if (change[2] == 'w') {
        mask |= S_IWOTH;
    } else if (change[2] == 'x') {
        mask |= S_IXOTH;
    } else {
        return -1;
    }

    if (change[0] == 'u') {
        mask <<= 6;
    } else if (change[0] == 'g') {
        mask <<= 3;
    } else if (change[0] == 'o') {
    } else {
        return -1;
    }

    if (change[1] == '+') {
        new_mode |= mask;
    } else if (change[1] == '-'){
        new_mode &= ~mask;
    } else {
        return -1;
    }

    return chmod(pathname, new_mode);
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    check_error(change_permition(argv[1], argv[2]) != -1, "permition");

    exit(EXIT_SUCCESS);
}
