//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-10-10
 */
extern int __VERIFIER_nondet_int(void);

int main(void) {
	int a[7][8][1+1+1];
	if (sizeof(a) != 7*8*3*sizeof(int)) {
		//@assert \false;
	}
	
	int n = __VERIFIER_nondet_int();
	if (n > 0) {
		int b[n];
		if (sizeof(b) != n * sizeof(int)) {
			//@assert \false;
		}
			
			
		if (n == 7*8*3) {
			if (sizeof(b) != sizeof(a)) {
				//@assert \false;
			}
		}
	}
	return 0;
}
