//Test for label encoding in unrolling example. This loop must be unrolled once to find the counterexample.

procedure main() {
	var x: bool;
	var y: int;
	
	x := true;
	y := 0;
	
	while(*)
	invariant (y != -1); {
		if (*) {
			if (x == true) {
				x := false;
			}
		} else if (*) {
			if ( false == x ) {
				y := y - 1;
			}
		}
	}
}