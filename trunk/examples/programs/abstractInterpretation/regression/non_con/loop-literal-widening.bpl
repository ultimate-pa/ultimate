//#Safe
procedure ULTIMATE.start()
{
	var x : int;
	x := 1;
	while (x < 100) {
		x := x + 1;
	}
	assert x <= 100;
}
