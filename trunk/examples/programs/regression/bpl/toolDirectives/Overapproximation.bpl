//#Unknown
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-14
//
// Test for the overapproximation tool directive that we pass to Ultimate via attributes.
//
// Our wiki says the following.
// If a function func has the attribute {:overapproximation "bar"} our model checkers will never output a counterexample that contains func.
// Instead our model checkers might say unknown and that an overapproximation of bar is the reason for saying unknown. 

function { :overapproximation "bitwiseAnd" } ~bitwiseAnd(in0 : int, in1 : int) returns (out : int);

procedure main() returns (#res : int){
    var x : int;
    var y : int;
    var z : int;

    y := 1;
    z := 2;
    x := ~bitwiseAnd(y, z);
    assert x == 0;
}


