//#Safe
/*
 *
 */

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
	call foo();
	assert old(x) == x - 1;
}

procedure foo()
modifies x;
{
	x := x + 1;
}
