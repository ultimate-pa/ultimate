// #Safe
/*
 * Test for bitwise operators in ACSL expressions
 * 
 * Date: 2023-09-20
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main(){
  int x = 42;
  //@ assert (x & 0) == 0;
  int y = 42;
  //@ assert (x | y) == x;
}
