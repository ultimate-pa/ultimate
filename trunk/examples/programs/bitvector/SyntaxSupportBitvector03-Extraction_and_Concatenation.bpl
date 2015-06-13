//#Safe
/* 
 * Extraction & Concatenation of bit vectors.
 * Author: langt@informatik.uni-freiburg.de
 * Date: 13.6.2015
 */

procedure Main() {
  assert(4bv5[3:1] == 2bv2);
  assert(2bv3 ++ 1bv5 == 65bv8);
  assert ((13bv6 ++ 4bv3)[5:2] == 3bv3);
}
