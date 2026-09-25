// #Safe
/*
 * Date: 2026-09-25
 * Author: schuessf@informatik.uni-freiburg.de
 */

struct S { int x; int entries[]; };

int main() {
  struct S *s1 = malloc(sizeof(struct S));
  if (s1 == NULL) return;
  s1->x = 5;
  struct S s2 = *s1;
  //@ assert s2.x == 5;
}
