#include "vcc.h"

int simultaneousDecrement(int i, int j)
requires(i >= 0)
requires(j >= 0)
{
	int x = i;
	int y = j;

	while(x > 0)
	{
		x = x - 1;
		y = y - 1;
	}

	if (i == j) {
		assert(y == 0);
	}
}