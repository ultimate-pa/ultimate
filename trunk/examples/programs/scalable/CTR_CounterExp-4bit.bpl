//#Safe

procedure ThreeBitCounter() {
	var x0, x1, x2, x3, of: bool;
	of := false;
	x0 := false;
	x1 := false;
	x2 := false;
	x3 := false;
	
	while(of == false) {
		if (x0 == true) {
			x0 := false;
			of := true;
		} else {
			x0 := true;
		}
		if (of == true) {
			if (x1 == true) {
				x1 := false;
			}
			else {
				x1 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x2 == true) {
				x2 := false;
			}
			else {
				x2 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x3 == true) {
				x3 := false;
			}
			else {
				x3 := true;
				of := false;
			}
		}
	}
	assert (!x0 && !x1 && !x2 && !x3);
}