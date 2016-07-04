//#Safe

procedure ULTIMATE.start()
{
	var x, y, z: int;

	assume x== 1 && y<=1 && y >=-1;
	assert true;
	z:= x / y ;
	assert true;
	assert z>=-1 && z<=2;
}
