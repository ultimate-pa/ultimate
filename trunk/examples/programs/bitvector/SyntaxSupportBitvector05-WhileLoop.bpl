//#Safe
/* 
 * While-loop modifying bit vector.
 * Author: langt@informatik.uni-freiburg.de
 * Date: 02.7.2015
 */

function{:builtin "bvadd"} BV2_ADD(x:bv2, y:bv2) returns (bv2);
function{:builtin "bvult"} BV2_ULT(x:bv2, y:bv2) returns (bool);

procedure Main() {
  var i:bv2;
  var a:bv2;
  i := 0bv2;
  a := 1bv2;
  
  while (BV2_ULT(i, 3bv2)) {
    a := BV2_ADD(a, 1bv2);
    i := BV2_ADD(i, 1bv2);
  }
  
  assert(a == 0bv2);
}
