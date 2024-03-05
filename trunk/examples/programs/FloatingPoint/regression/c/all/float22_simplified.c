// #Safe
/*
 * Minimal example to show unsoundness on the handling of unions in the
 * integer translation as found in svcomp/floats-cbmc-regression/float22.c
 * 
 * Date: 2024-02-28
 * Author: schuessf@informatik.uni-freiburg.de
 * 
 */

typedef union {
  int x;
  float y;
} type;

type cons() {
  type r;
  r.x = 0;
  return r;
}

int main() {
  type t;
  t = cons();
  int x = t.x;
  //@ assert x == 0;
}
