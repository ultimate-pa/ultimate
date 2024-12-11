// #Safe
/*
 * Date: 2024-11-12
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

struct s {
  union { int x; long y; };
};

int main() {
  struct s *p = malloc(sizeof(struct s));
  p->x = 5;
  //@ assert p->x == 5;
}
