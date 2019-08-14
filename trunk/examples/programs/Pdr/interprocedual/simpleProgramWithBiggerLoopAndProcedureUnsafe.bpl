// #Unsafe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 * Here we need interplants as the loop makes PDR not terminate.
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
		x := x + 1;
	}
    assert (x == 10);
}
