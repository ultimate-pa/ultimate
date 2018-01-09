/**
 * like ~01.c except that the with the dereferencing of r happens after r is 
 * havoced 
 *  --> thus the memory array may _not_ be separated in this program.
 */
int * nondet() {
  int *i;
  return i;
}

int main() {

  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));

  int *r = q;
  r = nondet();
  int z = *r;

  int x = *p;
  int y = *q;
}
