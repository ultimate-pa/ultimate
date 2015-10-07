//#Unsafe
/*
 * Author: ???
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */
procedure ThreeBitIncrementer() {
	var x0, x1, x2, of: bool;
	of := false;
	havoc x0;
	havoc x1;
	havoc x2;
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
	assert (x0 || x1 || x2);
}