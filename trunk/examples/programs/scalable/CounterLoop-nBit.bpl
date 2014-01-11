//#Safe

procedure nBitCounter() {
	var n, i, j, k, of:int;
	var x:[int]int;
	n := 100;
	assume(n > 0);
	
	i := 0;
	while (i < n) {
		x[i] := 0;
		i := i + 1;
	}
	
	while(true) {
		of := 1;
		j := 0;
		while(j < n) {
			if (of != 0) {
				if (x[j] == 1) {
					x[j] := 0;
					j := j + 1;
					if (j == n) {
						goto END;
					}
				}
				else {
					x[j] := 1;
					of := 0;
					goto LEND;
				}
			}
		}
		LEND:
	}
	END:
	
	assume(0 <= k && k < n);
	assert(x[k] == 0);
}