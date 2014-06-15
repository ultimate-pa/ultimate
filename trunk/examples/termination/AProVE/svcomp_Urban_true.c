/*
 * Terminating Program 
 *
 * Date: 18.12.2013
 * Author: urban@di.ens.fr
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x,y;
	while (x!=0 && y>0) {
	    if (x>0) {
		    if (__VERIFIER_nondet_int()) {
			    x = x - 1;
				y = __VERIFIER_nondet_int();
			} else {
			    y = y - 1;
			}
		} else {
		    if (__VERIFIER_nondet_int()) {
			    x = x + 1;
			} else {
			    y = y - 1;
				x = __VERIFIER_nondet_int();
			}		
		}
	}
}