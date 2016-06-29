//#Unsafe
// 29.06.16: Post is unsound because the term-transformation of the following triple is not valid: 
// {x = [ 1; 10 ]; y = [ 1; \infty ]; z = [ -\infty; \infty ]; } 
// assume true;assume x / y <= 4; 
// {x = [ 1; 10 ]; y = [ 1; 10 ]; z = [ -\infty; \infty ]; }

procedure ULTIMATE.start()
{
	var x, y, z : int;

	assume x>= 1 && x<=10 && y >=1;
	assert true;
	assume (x/y) <= 4 ;
	assert  y <= 10;
}
