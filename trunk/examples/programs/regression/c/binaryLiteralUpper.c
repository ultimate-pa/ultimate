//#Safe
/*
 * Date: 2025-05-05
 * Author: schuessf@informatik.uni-freiburg.de
 *
 * See https://github.com/ultimate-pa/ultimate/issues/715
 */

int main(void) {
  int b = 0B01011;
  //@ assert b == 11;
}
