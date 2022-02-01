// #Safe
// Reveals bug of issue #441.
// https://github.com/ultimate-pa/ultimate/issues/441
// Computations of pre, sp, wp, and interprocedural sequential composition
// forgot to handle auxiliary variables in call transition.
// 
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2019-08-20

var x,y : int;

procedure ULTIMATE.start() returns ()
modifies x, y;
{
	x := y;
	call y := proc(square(f())+x);
	assert y >= x;
}

procedure proc(i : int) returns (res : int) {
	res := i;
}

function { :overapproximation "myUnspecifiedOperation" } f() returns (out : int);

function square(in : int) : int {
	in*in
}
