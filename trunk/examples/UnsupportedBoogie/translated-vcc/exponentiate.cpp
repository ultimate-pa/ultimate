#include "vcc.h"
#include "math.h"


//Does not work!!!
unsigned int exponentiate(unsigned int x, unsigned int n)
ensures (result == pow(x,n))
{
	unsigned int a,b;
	unsigned int i;
	a = x;
	b = 1;
	i = n;
	while (i > 0)
		invariant (pow(x,n) == b * pow(a,i))
	{
		b = b * a;
		i = i - 1;
	}
	return b;
}

void main () {
}