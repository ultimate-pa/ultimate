//#Safe
/* 
 * Bit vector variant of the Goanna example.
 * Author: langt@informatik.uni-freiburg.de
 * Date: 02.7.2015
 */

function{:builtin "bvsub"} BV3_SUB(x:bv64, y:bv64) returns (bv64);
function{:builtin "bvsge"} BV3_SGE(x:bv64, y:bv64) returns (bool);

procedure Main() {
  var n:bv64;
  var p:bv64;

  assume p != 0bv64;

  while (BV3_SGE(n, 0bv64)) {
    assert(p != 0bv64);

    if (n == 0bv64) {
      p := 0bv64;
    }

    n := BV3_SUB(n, 1bv64);
  }
}
