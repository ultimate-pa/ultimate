//#Safe;NOPRELUDE

main() {
	int n, i, j, k, of;
	n = 100;
	if (n > 0) {
		int x[n];
		
		i = 0;
		while (i < n) {
			x[i] = 0;
			i = i + 1;
		}
		
		while(1) {
			of = 1;
			j = 0;
			while(j < n) {
				if (of != 0) {
					if (x[j] == 1) {
						x[j] = 0;
						j = j + 1;
						if (j == n) {
							goto END;
						}
					}
					else {
						x[j] = 1;
						of = 0;
						goto LEND;
					}
				}
			}
			LEND:
		}
		END:
		
		if(0 <= k && k < n){
			if(x[k] != 0) {ERROR: goto ERROR;}
		}
	}
	return 0;
}