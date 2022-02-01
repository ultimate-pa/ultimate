//#Unsafe
// 27.06.16: Rare bug during handling of modulo in interval domain

procedure ULTIMATE.start()
{
	var x, y, z : int;

	assume x>= 1 && x<=10;
	assert true;
	assume 
		(y % 2 == 0 && !(y == 0)) 
		&& ((((x - y <= 12 && -x - y <= 1) 
		&& y  >= -2) 
		&& x + y <= 12) 
		&& -x + y <= 1) 
		&& y - -y <= 4;

	assert  x / y == 5;
}
