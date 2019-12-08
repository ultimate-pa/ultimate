// #Safe
/* 
 * Simple Program for Checking PDRs interprocedual capabilities
 *
 */

var y : int;

procedure inc(z: int, q: int) returns (res: int)
{
	res := z + q;
	return;
}

procedure main() returns ()
modifies y;
{
    var x : int;
    assume (y == x);
    call y := inc(y, x);
    assert (y == x + 1);
}
