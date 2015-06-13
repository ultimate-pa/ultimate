//#Unsafe
/* 
 * Arithmetic operations on bit vectors.
 * Author: langt@informatik.uni-freiburg.de
 * Date: 13.6.2015
 */

function{:bvbuiltin "bvadd"} BV3_ADD(x:bv3, y:bv3) returns (bv3);
function{:bvbuiltin "bvsub"} BV3_SUB(x:bv3, y:bv3) returns (bv3);
function{:bvbuiltin "bvmul"} BV3_MUL(x:bv3, y:bv3) returns (bv3);
function{:bvbuiltin "bvudiv"} BV3_UDIV(x:bv3, y:bv3) returns (bv3);

procedure Main() {
  assert(BV3_ADD(2bv3, 4bv3) == 6bv3);
  assert(BV3_ADD(4bv3, 4bv3) == 0bv3);
  
  assert(BV3_SUB(6bv3, 2bv3) == 4bv3);
  assert(BV3_SUB(3bv3, 3bv3) == 0bv3);
  assert(BV3_SUB(2bv3, 4bv3) == 6bv3);
  
  assert(BV3_MUL(2bv3, 3bv3) == 6bv3);
  assert(BV3_MUL(4bv3, 2bv3) == 0bv3);
  
  assert(BV3_UDIV(6bv3, 3bv3) == 2bv3);
}
