//#Safe

procedure ThreeBitCounter() {
	var x0, x1, x2, x3, x4, x5, x6, x7, of: bool;
	of := false;
	x0 := false;
	x1 := false;
	x2 := false;
	x3 := false;
	x4 := false;
	x5 := false;
	x6 := false;
	x7 := false;
	
	while(of == false) {
		if (x0 == true) {
			x0 := true; //bug
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
		if (of == true) {
			if (x4 == true) {
				x4 := false;
			}
			else {
				x4 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x5 == true) {
				x5 := false;
			}
			else {
				x5 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x6 == true) {
				x6 := false;
			}
			else {
				x6 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x7 == true) {
				x7 := false;
			}
			else {
				x7 := true;
				of := false;
			}
		}
	}
	assert (!x0 && !x1 && !x2 && !x3 && !x4 && !x5 && !x6 && !x7);
}