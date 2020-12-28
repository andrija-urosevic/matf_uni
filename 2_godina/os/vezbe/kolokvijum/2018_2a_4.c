#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <errno.h>

#include <stdio.h>
#include <stdlib.h>

#define MAX_LEN 1000

#define check_error(expr, usermsg) \
    do { \
        if (!(expr)) { \
            exit(EXIT_FAILURE); \
        } \
    } while (0);

int move_words(const char* pathname1, const char* pathname2)
{
    FILE* f1 = fopen(pathname1, "r");
    check_error(f1 != NULL, "fopen");
    FILE* f2 = fopen(pathname2, "r+");
    check_error(f2 != NULL, "fopen");

    int off_set;
    char* word = malloc(MAX_LEN * sizeof (char));
    while (fscanf(f1, "%d %s", &off_set, word) != EOF) {
        fseek(f2, off_set, SEEK_SET);
        fprintf(f2, "%s", word);
    }
    free(word);

    fclose(f2);
    fclose(f1);

    return 1;
}

int main(int argc, const char *argv[])
{
    errno = EINVAL;
    check_error(argc == 3, "argumenti");
    errno = 0;

    check_error(move_words(argv[1], argv[2]), "move_words");

    exit(EXIT_SUCCESS);
}
