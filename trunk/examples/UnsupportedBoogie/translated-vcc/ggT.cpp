#include "vcc.h"

unsigned int ggT(unsigned int x, unsigned int y)
ensures (x % result == 0)
{
	unsigned int a, b;
	a = x;
	b = y;
	while (a != b)
	{
		if (a > b) a = a - b;
		else b = b - a;
	}
	return a;
}

void main() {
	unsigned int x, y;
	unsigned int result;
	result = ggT (x,y);
}