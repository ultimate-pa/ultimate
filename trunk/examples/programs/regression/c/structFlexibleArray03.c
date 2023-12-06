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
  struct str *s1 = malloc(sizeof (struct str) + 8);
  struct str *s2 = malloc(sizeof (struct str) + 2);
  int *dp = &(s1->d[0]);
  *dp = 42;
  *s1 = *s2;
  int res = s1->d[0];
  //@ assert res == 42;
}