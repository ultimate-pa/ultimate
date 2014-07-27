// Matthias: example that might reveal problems in translation
// and verification of the result.
// Delete this example if it seems to be redundant.

#include <stdlib.h>

struct Innermost {
   int i ;
};

struct Inner {
   struct Innermost *y ;
};

int main(void) {
  struct Innermost *imPtr = malloc(sizeof(struct Innermost)) ;
  struct Inner *inner = malloc(sizeof(struct Inner));
  struct Innermost *a ;
  struct Innermost *b ;
  struct Inner* p;
  
  
  inner->y = imPtr;
  
  a = inner->y;
  
  a->i = 4;
  
  b = inner->y;
  
    if (a != b) {
	ERROR: 
	  goto ERROR;
  } 
  
//   if (b->i != 4) {
// 	ERROR: 
// 	  goto ERROR;
//   } 
  
  return 0;
}
