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
	call inc();
	call inc();
	assert old(x) == x - 2;
}

procedure inc()
modifies x;
{
	x := x + 1;
}