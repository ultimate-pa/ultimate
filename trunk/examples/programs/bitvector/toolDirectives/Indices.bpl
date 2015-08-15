//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-14
//
// Test for the indices tool directive that we pass to Ultimate via attributes.
//
// Our wiki says the following.
// If a function ''func'' has the attribute {:indices k_1 k_2 ... k_n} where 
// each k_i is an IntegerLiteral the RCFGBuilder will translate foo to and SMT 
// function that has the indices k_1 k_2 ... k_n.
//
// In this examples, the list of indices is a singleton.

function { :builtin "sign_extend" } { :indices 2 } sign_extendFrom2To4(in0 : bv2) returns (out : bv4);

function { :builtin "sign_extend" } { :indices 96 } sign_extendFrom32To128(in0 : bv32) returns (out : bv128);

procedure main() returns (){
	var x : bv2;
	var y : bv4;
	
	var u : bv32;
	var v : bv128;

	x := 3bv2;     // 2 bit two's complement representation of -1
	y := sign_extendFrom2To4(x);
	assert y == 15bv4; // 4 bit two's complement representation of -1

	u := 4294967295bv32; // 32 bit two's complement representation of -1
	v := sign_extendFrom32To128(u);
	assert v == 340282366920938463463374607431768211455bv128; // 128 bit two's complement representation of -1
	
}


