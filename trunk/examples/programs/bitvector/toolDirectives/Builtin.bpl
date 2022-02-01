//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-14
//
// Test for the builtin tool directive that we pass to Ultimate via attributes.
//
// Our wiki says the following.
// If a function func has the attribute {:builtin "foo"} the RCFGBuilder will
// - assume that the SMT-LIB logic that the user selected has a function foo
// - translate the function func to an SMT function with the name foo. 
//
// Hence in this example the Boogie function foo will be translated in
// the SMT function "bvand"

function { :builtin "bvand" } foo(in0 : bv23, in1 : bv23) returns (out : bv23);

procedure main() returns (){
    var x : bv23;
    var y : bv23;
    var z : bv23;

    y := 1bv23;
    z := 2bv23;
    x := foo(y, z);
    assert x == 0bv23;
}


