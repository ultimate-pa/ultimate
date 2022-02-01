main() {
	int x0, x1, x2, x3, of;
	of = 0;
	x0 = 0;
	x1 = 0;
	x2 = 0;
	x3 = 0;
	of = 0;
	while(of == 0) {
		if (x0 == 1) {
			x0 = 0;
			of = 1;
		} else {
			x0 = 1;
		}
		if (of == 1) {
			if (x1 == 1) {
				x1 = 0;
			}
			else {
				x1 = 1;
				of = 0;
			}
		}
			if (of == 1) {
		if (x2 == 1) {
			x2 = 0;
		}
		else {
			x2 = 1;
			of = 0;
		}
		}
		if (of == 1) {
			if (x3 == 1) {
				x3 = 0;
			}
			else {
				x3 = 1;
				of = 0;
			}
		}
	}
	if (x0 != 0 || x1 != 0 || x2 != 0 || x3 != 0){ERROR: goto ERROR;}
}
