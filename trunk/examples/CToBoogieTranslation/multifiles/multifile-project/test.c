#include "foo.h"

extern int foo(int x);

int main()
{
	int x = 0;
	x = foo(x);
	//@assert x == 1;
	return 0;
}
