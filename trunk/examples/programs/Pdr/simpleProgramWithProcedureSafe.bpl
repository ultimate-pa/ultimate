// #Safe
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
    assume (y == x);
    call inc();
    assert (y == x + 1);
}
