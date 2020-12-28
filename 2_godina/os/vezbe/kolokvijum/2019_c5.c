#define _XOPEN_SOURCE 700
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <dirent.h>

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>

#define SEC_IN_DAY (60 * 60 * 24)

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

time_t now;

int obilazak(const char* pathname)
{
    struct stat sb;
    check_error(lstat(pathname, &sb) != -1, "stat");

    if (S_ISREG(sb.st_mode)) {
        time_t diff = ceil(difftime(now, sb.st_mtime) / SEC_IN_DAY);
        if (diff <= 5) {
            char* filename = strrchr(pathname, '/');
            if (filename != NULL) {
                printf("%s\n", filename + 1);
            } else {
                printf("%s\n", pathname);
            }
        }
    }

    if (!S_ISDIR(sb.st_mode)) {
        return 1;
    }
    
    DIR* dirp = opendir(pathname);
    if (dirp == NULL) {
        return -1;
    }

    struct dirent* entry;
    while ((entry = readdir(dirp)) != NULL) {
        char* new_pathname = malloc(strlen(pathname) + 1 +
                                    strlen(entry->d_name) + 1);

        strcpy(new_pathname, pathname);
        strcat(new_pathname, "/");
        strcat(new_pathname, entry->d_name);

        if ((strcmp(entry->d_name, ".") == 0) ||
             strcmp(entry->d_name, "..") == 0) {
            free(new_pathname);
            continue;
        }

        int success = obilazak(new_pathname);
        free(new_pathname);
        if (!success) {
            return -1;
        }
    }

    return closedir(dirp) == 0;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat");
    check_error(S_ISDIR(sb.st_mode), "nije dir");

    now = time(NULL);

    check_error(obilazak(argv[1]) != -1, "obilazak");

    exit(EXIT_SUCCESS);
}
