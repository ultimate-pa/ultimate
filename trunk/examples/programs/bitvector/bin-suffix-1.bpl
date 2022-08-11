//#Safe
/* 
 * Boogie version of the SV-COMP benchmark
 * loop-invariants/bin-suffix-5.c
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2022-01-07
 */


procedure main() returns (){
    var x : bv2;

    x := 1bv2;
    while (*)
    {
        x := ~bvadd2(2bv2, x);
    }
    assert(1bv2 == ~bvand2(1bv2, x));
}



function { :builtin "bvadd" } ~bvadd2(in0 : bv2, in1 : bv2) returns (out : bv2);
function { :builtin "bvand" } ~bvand2(in0 : bv2, in1 : bv2) returns (out : bv2);
