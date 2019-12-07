//#Safe
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
    x := 23;
	g := 0;

    fork 1 foo(x);

}

procedure foo(n : int) returns(res : int)
modifies g;
{
	fork 2 bar(n);
	call increment();
}


procedure bar(n : int) returns(res : int)
modifies g;
{
	assert n == 23;
	call increment();
}

procedure increment() returns ();
ensures g == old(g) + 1;
modifies g;
