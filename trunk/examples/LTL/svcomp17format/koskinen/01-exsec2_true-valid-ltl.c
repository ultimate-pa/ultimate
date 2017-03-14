// Based on the small program from section 2 of the paper "Cook, Koskinen: Making Prophecies with Decision Predicates"
// manually translated by DD
//
// Property is taken from Table 1


extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int x;

void main()
{
	x = 1;
	while (__VERIFIER_nondet_int()) {}	
	
	x = 0;
	x = 1;
	while (1) {}
}

