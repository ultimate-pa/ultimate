procedure foo() {
	var LOC_ID:int;
	var x: real;
	x := 0.0;
	
	while(*) {
		x := 0.0;
		if (x==0.0) {
			x := 1.0;
		} else {
			x := 0.0;
		}
	}
	assert LOC_ID == 0;
}