#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <dirent.h>

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int min_max_size(const char* pathname, int* min_size, int* max_size)
{
    struct stat sb;
    check_error(stat(pathname, &sb) != -1, "stat");

    if (*min_size > sb.st_size) {
        *min_size = sb.st_size;
    }

    if (*max_size < sb.st_size) {
        *max_size = sb.st_size;
    }

    if(!S_ISDIR(sb.st_mode)) {
        return 1;
    }

    DIR* dirp = opendir(pathname);
    if (dirp == NULL) {
        return -1;
    }

    struct dirent* entry = NULL;
    while ((entry = readdir(dirp)) != NULL) {
        char* new_pathname = malloc(sizeof (pathname) + 2 +
                                    sizeof (entry->d_name));

        strcpy(new_pathname, pathname);
        strcat(new_pathname, "/");
        strcat(new_pathname, entry->d_name);

        if (strcmp(entry->d_name, ".") == 0 || 
            strcmp(entry->d_name, "..") == 0) {
            if (stat(entry->d_name, &sb) == -1) {
                free(new_pathname);
                return -1;
            }

            if (*min_size > sb.st_size) {
                *min_size = sb.st_size;
            }
            if (*max_size < sb.st_size) {
                *max_size = sb.st_size;
            }

            free(new_pathname);
            continue;
        }

        int success = min_max_size(new_pathname, min_size, max_size);
        free(new_pathname);
        if (!success) {
            return -1;
        }
    }

    if (closedir(dirp) == -1) {
        return -1;
    }

    return 1;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 2, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat");
    
    check_error(S_ISDIR(sb.st_mode), "not dir");

    int max = sb.st_size;
    int min = sb.st_size;

    check_error(min_max_size(argv[1], &min, &max), "min_max_size");

    printf("%d\n", max - min);
    exit(EXIT_SUCCESS);
}
