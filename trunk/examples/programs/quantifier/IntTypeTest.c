//#Unsafe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012
void meth(void) {
	int i = 0;
	i = 0L; // long
	i = 0uLL; // unsinged long long
	i = -072; //octal!
	i = 456789;
	i = 4u; //unsigned
	i = -0x9A; // hex
	long j = 0;
	unsigned long k = 0;
	long long l = (long) 3;
	int divZero = i / 0;
	divZero = i / j;
	divZero /= j;
}
