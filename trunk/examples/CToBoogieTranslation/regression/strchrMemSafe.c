//#Safe
#include <stdlib.h>

int main() {
  char *string = malloc(8);

  char * i = __builtin_strchr(string, 3);

  free(string);
}
