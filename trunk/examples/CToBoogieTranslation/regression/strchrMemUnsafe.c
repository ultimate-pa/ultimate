//#Unsafe
#include <stdlib.h>

int main() {
  char *string;

  char * i = __builtin_strchr(string, 3);

  free(string);
}

