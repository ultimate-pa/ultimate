//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-15
*/

int main() {
  int x;
  if (__alignof__(unsigned long) == __alignof__(unsigned long long)) {
    x = 1;
  } else {
    x = 2;
  }
  //@assert x > 0;
}