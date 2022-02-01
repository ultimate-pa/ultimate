procedure main(){
	var pc, input, req, current, max: int;
	
	assume(current <= max);
	assume(input <= max);
	
	pc := 0;
	
	while(*)
	invariant(current <= max); {
		
		// REQUEST
		if (pc == 0) {
			pc := 1;
			req := input;
		}
		
		// INIT
		if (pc == 1) {
			if (req > current) {
				// UP
				pc := 2;
			} else if (req < current) {
				// DOWN
				pc := 3;
			} else if (req == current) {
				// READY
				pc := 0;
				havoc input;
				assume(input <= max);
			}
		}
		
		//MOVEUP
		if (pc == 2) {
			if (req > current) {
				// UP
				current := current + 1;
			} else if (req == current) {
				// READY
				pc := 0;
				havoc input;
				assume(input <= max);
			}
		}
		
		//MOVEDOWN
		if (pc == 3) {
			if (req < current) {
				// DOWN
				current := current - 1;
			} else if (req == current) {
				// READY
				pc := 0;
				havoc input;
				assume(input <= max);
			}
		}
	}
}