// #Safe
/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Bitvector operation should result in an overapproximation flag.
 */
extern int __VERIFIER_nondet_int();

int main() {
    int i = __VERIFIER_nondet_int();
	if (i) {
	  i = 1 & 2;
	} else {
	  i = 0;
	}
    if (i != 0) {
        //@ assert \false;
    }
}
