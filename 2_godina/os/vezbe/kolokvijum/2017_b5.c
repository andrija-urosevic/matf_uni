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

const char* ext;

int obilazak(const char* filepath, size_t* count)
{
    struct stat sb;
    check_error(lstat(filepath, &sb) != -1, "stat");

    if (!S_ISDIR(sb.st_mode)) {
        char* file_ext = strrchr(filepath, '.');
        if (file_ext != NULL) {
            if (strcmp(file_ext, ext) == 0) {
                (*count)++;
            }
        }
        return 1;
    }

    DIR* dirp = opendir(filepath);
    check_error(dirp != NULL, "opendir");

    struct dirent *entry;
    while ((entry = readdir(dirp)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 ||
            strcmp(entry->d_name, "..") == 0) {
            continue;
        }

        char* new_filepath = malloc(sizeof (filepath) + 1 +
                                    sizeof (entry->d_name) + 1);

        strcpy(new_filepath, filepath);
        strcat(new_filepath, "/");
        strcat(new_filepath, entry->d_name);

        int success = obilazak(new_filepath, count);
        free(new_filepath);

        if (!success) {
            return -1;
        }
    }

    return closedir(dirp) == 0;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    struct stat sb;
    check_error(stat(argv[1], &sb) != -1, "stat");
    check_error(S_ISDIR(sb.st_mode), "nije dir");

    ext = argv[2];

    size_t count = 0;
    check_error(obilazak(argv[1], &count) != -1, "obilazak");
    printf("%d\n", count);

    exit(EXIT_SUCCESS);
}
