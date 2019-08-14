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
}


procedure main() returns ()
modifies y;
{
    var x : int;
	x := 0;
    assume (y == x);
	while (y < 10) {
		call inc();
	}
    assert (y == 11);
}
