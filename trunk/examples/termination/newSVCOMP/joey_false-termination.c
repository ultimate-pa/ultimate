/* A non-terminating example, given to me by Joey Feldberg
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */

extern int __VERIFIER_nondet_int(void);

int rec(int x) {
    if (x <= 0) {
	  return x;
	} else if (x%2 == 0) {
      return rec(x/2);
    } else {
      return rec(++x) + rec(--x);
    }
}

int main() {
    int x = __VERIFIER_nondet_int();
    int y;
	y = rec(x);
}
