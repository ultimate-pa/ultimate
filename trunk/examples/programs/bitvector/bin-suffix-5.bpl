//#Safe
/* 
 * Boogie version of the SV-COMP benchmark
 * loop-invariants/bin-suffix-5.c
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2022-01-07
 */


procedure main() returns (){
    var x : bv32;

    x := 5bv32;
    while (*)
    {
        x := ~bvadd32(8bv32, x);
    }
    assert(5bv32 == ~bvand32(5bv32, x));
}



function { :builtin "bvadd" } ~bvadd32(in0 : bv32, in1 : bv32) returns (out : bv32);
function { :builtin "bvand" } ~bvand32(in0 : bv32, in1 : bv32) returns (out : bv32);
