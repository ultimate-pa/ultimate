//#Safe
procedure Easy() {
	var x: int;
	
	havoc x;	
	x := 0;
	
	assert (x < 1);
}