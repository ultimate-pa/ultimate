// #Safe
/*
 * Date: 2025-02-12
 * Author: schuessf@informatik.uni-freiburg.de
 */

int main() {
  int* p = malloc(sizeof(int));
  if (p == NULL) return;
  //@ assert p != \null;
}
