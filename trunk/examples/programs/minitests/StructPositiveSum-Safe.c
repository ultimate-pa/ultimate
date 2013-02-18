/* #mSafe
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 08.02.2012
 * simple example where structs occur in loop invariant
 */

typedef struct {
	int fst;
	int snd;
} pair;

int main(void) {
    pair a = { .fst = 23, .snd = 42 };
    int cond;
    while (cond) {
        int nondet1;
        cond = nondet1;
	int nondet2;
	if (nondet2) {
	    a.fst++;
	    a.snd--;
	} else {
	    a.fst--;
	    a.snd++;
	}
    }
    //@ assert a.fst+a.snd >= 0;
    return 0;
}