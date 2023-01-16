//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-10-20
*/

typedef long unsigned int size_t;
void * __attribute__((__cdecl__)) malloc (size_t __size) ;
extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));

int main() {
  unsigned int size = 4294967295;
  int *a = malloc(sizeof(int) * size);
  a[0] = 5;
  int x = a[0];
  free(a);
}