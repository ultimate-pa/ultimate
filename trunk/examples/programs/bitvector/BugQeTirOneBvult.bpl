//#Safe
/* 
 * Reveals bug in TIR for bitvectors.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2020-03-11
 */
procedure ULTIMATE.start() returns (){
    var x : bv32;
    var z : bool;
    var y : bv32;

	assume x == 0bv32;
    z := ~bvult32(y, x);
    assert !z;

}

function { :builtin "bvult" } ~bvult32(in0 : bv32, in1 : bv32) returns (out : bool);
