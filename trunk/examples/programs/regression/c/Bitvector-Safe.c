/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Bitvector operation should result in an overapproximation flag.
 */
int main() {
    int i;
	if (i) {
	  i = 1 & 2;
	} else {
	  i = 0;
	}
    if (i != 0) {
        //@ assert \false;
    }
}
