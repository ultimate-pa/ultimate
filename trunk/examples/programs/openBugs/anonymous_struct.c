// #Safe
/*
 * Date: 2024-11-12
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

union u {
  struct { int x; };
};

int main(){
  union u *p = malloc(sizeof(union u));
  p->x = 2;
  //@ assert p->x == 2;
}
