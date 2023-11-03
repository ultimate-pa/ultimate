//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-15
  
  We are not able to verify this yet, since we just use an imprecise overapproximation.
*/

int main() {
  int x;
  if (__alignof__(unsigned long) == __alignof__(unsigned long)) {
    x = 1;
  } else {
    x = 2;
  }
  //@assert x == 1;
}