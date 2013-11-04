/*
 * Problem, if not both, im and inner are malloced, then address of inner and 
 * value of inner.y may be the same and the assignment
 *    a->i = 4
 * changes the address of inner (which is a local heap value in our translation)
 * 
 * November 2013
 * Matthias & Christian
 */



struct Innermost {
   int i ;
};

struct Inner {
   struct Innermost *y ;
};

int main(void) {
  struct Innermost im ;
  struct Inner inner;
  struct Innermost *a ;
  struct Innermost *b ;
  struct Inner* p;
  
  inner.y = & im;
  
  a = inner.y;
  
  a->i = 4;
  
  b = inner.y;
  
    if (a != b) {
	ERROR: 
	  goto ERROR;
  } 
  
  return 0;
}
