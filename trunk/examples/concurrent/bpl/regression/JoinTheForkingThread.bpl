//#Unsafe
/*
 * 
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-10-22
 * 
 */

var g : int;


procedure ULTIMATE.start()
modifies g;
{
    var x : int;
    x := 0;
	g := 0;

    fork 1 foo(x);
    join 2;
	
	assert g == 0;
}

procedure foo(n : int) returns(res : int)
modifies g;
{
	fork 2 bar(n);
	g := g + 1;
	res := 23;
}


procedure bar(n : int) returns(res : int)
{
	var nondet : int;
	var localVar : int;
	
	res := 23;
	// assign the return value to a local variable
	// in order to reproduce the bug that was fixed
	// with commit 782a520123106edbc0affe3a0b0f459529f09a8e
	join nondet assign localVar;
	assert false;
}
