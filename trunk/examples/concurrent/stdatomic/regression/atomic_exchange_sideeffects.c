//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-07-19
 */

int main(void) {
  int c = 0;
  int x[2] = {0, 1};
  int y = 1;
  int z = 2;
  __atomic_exchange(x + c++, &y, &z, 5);
  //@ assert c == 1;
  //@ assert x[0] == 1 && y == 1 && z == 0;
}
