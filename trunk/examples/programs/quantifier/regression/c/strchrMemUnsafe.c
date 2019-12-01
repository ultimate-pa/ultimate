//#Unsafe
/*
 * call to strchr with a unallocated pointer 
 * --> program is memory unsafe
 *
 * author: Alexander Nutz
 */
#include <stdlib.h>
#include <string.h>

int main() {
  char *string;

  char * j = strchr(string, 3);

  free(string);
}

