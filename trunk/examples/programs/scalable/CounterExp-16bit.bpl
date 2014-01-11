//#Safe

procedure ThreeBitCounter() {
	var x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, of: bool;
	of := false;
	x0 := false;
	x1 := false;
	x2 := false;
	x3 := false;
	x4 := false;
	x5 := false;
	x6 := false;
	x7 := false;
	x8 := false;
	x9 := false;
	x10 := false;
	x11 := false;
	x12 := false;
	x13 := false;
	x14 := false;
	x15 := false;
	
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
		if (of == true) {
			if (x8 == true) {
				x8 := false;
			}
			else {
				x8 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x9 == true) {
				x9 := false;
			}
			else {
				x9 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x10 == true) {
				x10 := false;
			}
			else {
				x10 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x11 == true) {
				x11 := false;
			}
			else {
				x11 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x12 == true) {
				x12 := false;
			}
			else {
				x12 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x13 == true) {
				x13 := false;
			}
			else {
				x13 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x14 == true) {
				x14 := false;
			}
			else {
				x14 := true;
				of := false;
			}
		}
		if (of == true) {
			if (x15 == true) {
				x15 := false;
			}
			else {
				x15 := true;
				of := false;
			}
		}
	}
	assert (!x0 && !x1 && !x2 && !x3 && !x4 && !x5 && !x6 && !x7 && !x8 && !x9 && !x10 && !x11 && !x12 && !x13 && !x14 && !x15);
}