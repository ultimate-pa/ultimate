//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

int main() {
  unsigned char a = 128U;
  unsigned char b = 1U;
  int i = a << b;
  //@ assert i == 256;
}
