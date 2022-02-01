// #Safe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 *
 */

var y : int;

procedure inc(z: int) returns (res: int)
{
	res := z + 1;
	return;
}

procedure main() returns ()
modifies y;
{
    var x : int;
    assume (y == x);
    call y := inc(y);
    assert (y == x + 1);
}
