extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * recHanoi.c
 *
 *  Created on: 17.07.2013
 *      Author: Stefan Wissert
 */

extern int __VERIFIER_nondet_int(void);

int counter;
/*
 * This function returns the optimal amount of steps,
 * needed to solve the problem for n-disks
 */
int hanoi(int n) {
	if (n == 1) {
		return 1;
	}
	return 2 * (hanoi(n-1)) + 1;
}

/*
 * This applies the known algorithm, without executing it (so no arrays).
 * But the amount of steps is counted in a global variable.
 */
void applyHanoi(int n, int from, int to, int via)
{
	if (n == 0) {
		return;
	}
	// increment the number of steps
	counter++;
	applyHanoi(n-1, from, via, to);
	applyHanoi(n-1, via, to, from);
}

int main() {
    int n = __VERIFIER_nondet_int();
    if (n < 1 || n > 31) {
    	return 0;
    }
    counter = 0;
    applyHanoi(n, 1, 3, 2);
    int result = hanoi(n);
    // result and the counter should be the same!
    if (result == counter) {
        return 0;
    } else {
        ERROR: __VERIFIER_error();
    }
}



