#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>
#include <dirent.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int obilazak(const char* pathname)
{
    struct stat sb;
    check_error(lstat(pathname, &sb) != -1, "stat");

    if (S_ISREG(sb.st_mode)) {
        if ((strncmp(pathname, "dir_", 4 * sizeof (char)) == 0) ||
            (strstr(pathname, "/dir_") != NULL)) {
            char* filename = NULL;
            if ((filename = strrchr(pathname, '/')) != NULL) {
                printf("%s\n", filename + 1);
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

    struct dirent *entry;
    while ((entry = readdir(dirp)) != NULL) {
        char* new_pathname = malloc(strlen(pathname) + 1 + 
                                    strlen(entry->d_name) + 1);

        if (new_pathname == NULL) {
            return -1;
        }

        strcpy(new_pathname, pathname);
        strcat(new_pathname, "/");
        strcat(new_pathname, entry->d_name);

        if (strcmp(entry->d_name, "..") == 0 || 
            strcmp(entry->d_name, ".") == 0) {
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

    check_error(obilazak(argv[1]) != -1, "obilazak");

    exit(EXIT_SUCCESS);
}
