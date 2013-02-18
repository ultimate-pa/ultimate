#include "vcc.h"

void simpleLoop(int* x, unsigned int l)
requires(is_array(x,l))
writes(array_range(x,l))
ensures(forall(unsigned int i; (0 <= i && i < l) ==> (x[i] == 0)))
{
	unsigned int i = 0;
	while (i < l)
	invariant(forall(unsigned int j; (0 <= j && j < i) ==> (x[j] == 0)))
	{
		x[i] = 0;
		i++;
	}
}