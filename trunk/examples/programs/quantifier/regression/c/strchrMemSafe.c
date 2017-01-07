//#Safe
/*
 * call to strchr with a correctly allocated pointer 
 * --> program is memory safe
 *
 * author: Alexander Nutz
 */
#include <stdlib.h>

int main() {
  char *string = malloc(8);

  char * i = __builtin_strchr(string, 3);
  char * j = strchr(string, 3);

  free(string);
}
