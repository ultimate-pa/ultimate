// #Unsafe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 *
 */

var y : int;

procedure inc() returns () 
modifies y;
{
	y := y + 1;
	call inc2();
}

procedure inc2() returns () 
modifies y;
{
	y := 2;
}


procedure main() returns ()
modifies y;
{
    var x : int;
    assume (y == x);
    call inc();
    assert (y != 2);
}
