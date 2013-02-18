#include <vcc.h>
#include <limits.h>

int adda (int a, int b)
{
	return a+b;
}

int addb (int a, int b)
requires(a + b <= INT_MAX)
{
	return a+b;
}

int addc (int a, int b)
requires(a + b >= INT_MIN)
requires(a + b <= INT_MAX)
{
	return (a+b);
}