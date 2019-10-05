// #Safe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 *
 */

var y: int;
var z: int;

procedure inc() returns () 
modifies y;
{
	y := 2;
}


procedure main() returns ()
modifies y;
{
    call inc();
    assert (y == 2);
}
