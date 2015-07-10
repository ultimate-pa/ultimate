/*
 * Program from Fig.1a of
 * 2006CAV - Gopan,Reps - Lookahead Widening
 *
 * Date: 2014-06-22
 * Author: Caterina Urban, Matthias Heizmann
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y;
	x = 0;
    y = 0;
	while (y >= 0) {
		if (x <= 50) {
			y = y + 1;
		} else {
			y = y - 1;
		}
		x = x + 1;
	}
	return 0;
}
