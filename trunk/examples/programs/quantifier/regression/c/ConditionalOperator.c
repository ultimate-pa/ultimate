/* #Safe
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-19
 * Tests for Conditional operator as defined in C11 6.5.15
 */

extern int __VERIFIER_nondet_int(void);

int g = 23;

void inc(void) {
	g++;
}

void dec(void) {
	g--;
}


int main(void) {
	char c = 'a';
	char *p;
	// the following two lines helped us to reproduce a bug 
	// that was fixed in 98d185d53639417ddb6989541bb3ce70423da031
	p = 0 ? 0 : &c;
	p = 0 ? &c : 0;
	
	int b = __VERIFIER_nondet_int();
	b ? inc() : dec();
	//@ assert ((b == 0) ==> g == 22) && ((b != 0) ==> g == 24);
	
	return 0;
}
