//#Safe
/*
 *
 */

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
	x:=1;
	call foo();
}

procedure foo()
modifies x;
{
	assert old(x) == x ;
}