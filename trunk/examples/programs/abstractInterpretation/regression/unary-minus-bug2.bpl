//#Safe
// 27.06.16: Handling of unary minus 

procedure ULTIMATE.start()
{
	var x, y, z : int;

	assume -y + -y <= 4;
	assert y >= -2 ;

}
