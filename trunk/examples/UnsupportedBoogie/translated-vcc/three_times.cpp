#include "vcc.h"
#include <limits.h>

int three_times(int n)
requires(n >= 0)
requires(3*n < 0x7fffffff)
ensures(result == 3*n)
{
	int s = 0;
	int i = 0;
	//while(i != n)
	while(i < n)
		invariant (s == i * 3)
		invariant (i <= n)
	{
		s = s + 3;
		i = i + 1;
	}
	assert(i == n);
	return s;
}