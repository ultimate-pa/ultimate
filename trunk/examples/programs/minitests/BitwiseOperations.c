// #Unsafe
/*
 * Translate bitwise operations to uninterpreted funtion symbols.
 * 
 * Date: 19.10.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 *
 */

int main(void) {
  int x, y, z;
  y = 1;
  z = 2;
  x = x & y;
  x = x | y;
  x = x ^ y;
  x = x << y;
  x = x >> y;
  x &= y;
  x |= y;
  x ^= y;
  x <<= y;
  x >>= y;
  if (x == 1) {
    ERROR:
    goto ERROR;
  }
}