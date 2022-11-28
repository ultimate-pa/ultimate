//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-15
*/

extern int abs (int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;

int main() {
  int x;
  if (x > -100000 && abs(x) < 0) {
    //@assert 0;
  }
}