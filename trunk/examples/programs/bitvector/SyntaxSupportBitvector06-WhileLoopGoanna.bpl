//#Safe
/* 
 * Bit vector variant of the Goanna example.
 * Author: langt@informatik.uni-freiburg.de
 * Date: 02.7.2015
 */

function{:builtin "bvsub"} BV3_SUB(x:bv3, y:bv3) returns (bv3);
function{:builtin "bvsge"} BV3_SGE(x:bv3, y:bv3) returns (bool);

procedure Main() {
  var n:bv3;
  var p:bv3;

  assume p != 0bv3;

  while (BV3_SGE(n, 0bv3)) {
    assert(p != 0bv3);

    if (n == 0bv3) {
      p := 0bv3;
    }

    n := BV3_SUB(n, 1bv3);
  }
}
