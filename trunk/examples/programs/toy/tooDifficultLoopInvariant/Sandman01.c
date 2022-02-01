//#Safe
/*
 * Motivating example for hierarchical trace abstraction.
 * Maybe correct name is Brazil.
 * 
 * Date: 2016-11-22
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */


extern double __VERIFIER_nondet_double(void);
extern int __VERIFIER_nondet_int(void);
extern unsigned char __VERIFIER_nondet_uchar(void);


int main() {
	double f = __VERIFIER_nondet_double();
	int a[512];
	int i = __VERIFIER_nondet_int();
	signed char c = i;
	unsigned char j = __VERIFIER_nondet_uchar();
	unsigned int x = 128 + c;
	unsigned int y = 128 + j;
	
	if (f != 0.0) {
		a[x] = 0;
		a[y] = 1000;
	}
	while (__VERIFIER_nondet_int()) {
		a[x] = a[x] + 1;
		a[y] = a[y] - 1;
		f = f + 1.0;
	}
	if (!(f >= 0.0) && c < 0) {
		if (a[x] == 1000 && a[y] != 0) {
			//@ assert \false;
		}
	}
	
	return 0;
}





// 
// if (i % 256 < 128) {
//     c := i % 256;
// } else {
//     c := (i % 256) - 256;
// }
