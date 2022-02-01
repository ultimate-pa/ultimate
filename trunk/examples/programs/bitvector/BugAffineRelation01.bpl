//#Safe
/* 
 * Reveals bug in AffineRelation for bitvectors.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-02-26
 */

type { :isUnsigned false } { :bitsize 32 } C_INT = bv32;

implementation main() returns (){
    var len : C_INT;
    var c : C_INT;

    assume (c == ~bvsub32(len, 1bv32));
	while (*) {
		// break large block encoding
	}
    if (c == ~bvsub32(len, 1bv32)) {
        goto END;
    }
    assert(false);
  END:
    return;
}


procedure main() returns ();
modifies ;


function { :builtin "bvsub" } ~bvsub32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
