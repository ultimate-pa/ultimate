//#Safe
/*
 * 
 * Date: 2019-04-12
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 */
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main(void) {
	unsigned int x = 1;
	unsigned int y = 1;
	// loop until x's value is in the first half of the numbers that
	// an unsigned int can have on an x86 computer
	//@ loop invariant (x % 2 == 1 && y % 2 == 1);
	while(x < 256*256*256*254U) {
		// choose nondeterministically between if-branch and else-branch
		if (__VERIFIER_nondet_int()) {
			// note that in C11 unsigned ints cannot overflow,
			// because the result is always the remainder of
			// an euclidean division with the successor of the
			// largest natural number that an unsigned int can store
			x = 3 * x;
			y = -2 * y + 1;
		} else {
			// swap the values of x and y
			unsigned int tmp = x;
			x = y;
			y = tmp;
		}
	}
	// the program is correct if y is never four at the end
	// of the loop
	if (y == 4) {
		__VERIFIER_error();
	}
	return 0;
}

