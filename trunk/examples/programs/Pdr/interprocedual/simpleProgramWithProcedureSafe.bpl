// #Safe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 * Here, the the query for the recursive PDR going through inc() is sat.
 * meaning true /\ y' = y + 1 /\ y' != x' + 1 is sat
 * so that we backtrack out of the procedure to the assumption which then
 * gets unsat.
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
