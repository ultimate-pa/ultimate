// #Safe
/*
 * Date: 2023-11-14
 * Author: schuessf@informatik.uni-freiburg.de
 */

struct str {
  int n;
  int d[];
};

int main() {
  struct str *s = malloc(sizeof (struct str) + 8);
  int *dp = &(s->d[0]);
  *dp = 42;
  int res = s->d[0];
  //@ assert res == 42;
}