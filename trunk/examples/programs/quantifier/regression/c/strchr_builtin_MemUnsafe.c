//#Unsafe
/*
 * call to strchr with a unallocated pointer 
 * --> program is memory unsafe
 *
 * author: Alexander Nutz
 */
#include <stdlib.h>

int main() {
  char *string;

  char * i = __builtin_strchr(string, 3);

  free(string);
}

