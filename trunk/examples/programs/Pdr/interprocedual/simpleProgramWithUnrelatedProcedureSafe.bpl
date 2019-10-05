// #Safe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 *
 * Here, the the query for the recursive PDR going through inc() is unsat.
 * meaning true /\ y' = 2 /\ y' != 2 is unsat
 * testing how the main PDR updates its frames.
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
