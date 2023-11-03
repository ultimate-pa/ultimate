//#Safe
/* 
 * Bug: In counterexample, variable k has initially value
 * 2147483649bv32. The signed inequality 
 * bvsge(2147483649bv32, 1bv32) is however equivaent to false.
 * 
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2021-12-07
 */

implementation main() returns (){
    var k : bv32;

    assume ~bvsge32(k, 1bv32);
	while (*) {}
    k := ~bvsub32(k, 1bv32);
	while (*) {}
    assert ~bvsge32(k, 0bv32);
}

procedure main() returns ();
modifies ;

function { :builtin "bvsge" } ~bvsge32(in0 : bv32, in1 : bv32) returns (out : bool);
function { :builtin "bvsub" } ~bvsub32(in0 : bv32, in1 : bv32) returns (out : bv32);
function { :builtin "bvadd" } ~bvadd32(in0 : bv32, in1 : bv32) returns (out : bv32);
