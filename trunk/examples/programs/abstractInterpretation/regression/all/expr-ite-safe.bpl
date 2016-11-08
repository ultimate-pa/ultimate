//#Safe
/*
 * Tests if-then-else expressions.
 */

procedure ULTIMATE.start()
{
	var x : int;
	var y : int;

	y := (if x > 0 then 1 else -1);

	assert(true);
}
