//#Safe
procedure ULTIMATE.start() {
	var x, y, rel: int;
	
	havoc x, y;
	assume 2 <= x + y && y + x <= 4;
	rel := x + y;
	assert 2 <= rel && rel <= 4;
	
	havoc x, y;
	assume -3 <= x - y && x - y <= -1;
	rel := x - y;
	assert -3 <= rel && rel <= -1;
	
	havoc x, y;
	assume -2 <= y - x && y - x <= 3;
	rel := y - x;
	assert -2 <= rel && rel <= 3;
}
