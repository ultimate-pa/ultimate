// #Safe
/*-----------------------------------------------------------------------------
 * Accessing a member of an anonymous union nested in a struct.
 *-----------------------------------------------------------------------------
 *   Date: 2024-11-12
 * Author: schuessf@informatik.uni-freiburg.de
 *---------------------------------------------------------------------------*/

struct s {
  union { int x; long y; };
};

int main() {
  struct s *p = malloc(sizeof(struct s));
  if (p == NULL) return -1;
  p->x = 5;
  //@ assert p->x == 5;
  long *yp = &p->y;
  //@ assert \valid(yp);
  return 0;
}
