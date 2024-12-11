//#Safe
/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-02-30
 * 
 */

int main() {
  int x = __VERIFIER_nondet_int();
  int y = ({ x ? ({ x; }) : 0; });
  //@ assert x == y;
}