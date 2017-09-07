//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * gcd program (terminating) based on 
 * (Dershowitz, Lindenstrauss, Sagiv and Serebrenik, 2001)
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	int r, x, y;

	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();

	if (x<0) {x = -x;}
	if (y<0) {y = -y;}
	while (y>0) {
		/*  the next statements compute  r = mod(x,y)   */
		r = x;
		while (r>=y) {
			r = r-y;
        }
		/* end of inlined mod */
		x = y;
		y = r;
	}
    return 0;
}
