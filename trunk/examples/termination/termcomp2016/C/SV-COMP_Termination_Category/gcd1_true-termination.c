/*
 * gcd program (terminating) based on 
 * (Dershowitz, Lindenstrauss, Sagiv and Serebrenik, 2001)
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */
extern int __VERIFIER_nondet_int(void);

int gcd(int x, int y)	
{
	int r;
	
	if (x<0) x = -x;
	if (y<0) y = -y;
	while (y>0) {
		/*  the next statements compute  r = mod(x,y)   */
		r = x;
		while (r>=y) 
			r = r-y;
		/* end of inlined mod */
		x = y;
		y = r;
	}
	return x;
}

int main()
{
	int x,y;

	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();

	gcd(x,y);
}


