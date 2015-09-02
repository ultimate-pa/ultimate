//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

int main() {
  int a = -1;
  int b = a >> 1;
  //@ assert b == -1;
}
