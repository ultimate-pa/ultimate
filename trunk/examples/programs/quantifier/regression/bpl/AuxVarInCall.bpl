// #Safe
// Reveals bug of issue #441.
// https://github.com/ultimate-pa/ultimate/issues/441
// Computations of sp and wp forgot to handle auxiliary variables
// in call transition.
// 
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2019-08-20

procedure ULTIMATE.start() returns () {
	call proc(square(f()));
}

procedure proc(i : int) returns () {
	assert i >= 0;
}

function { :overapproximation "myUnspecifiedOperation" } f() returns (out : int);

function { :inline "true" } square(in : int) : int {
	in*in
}
