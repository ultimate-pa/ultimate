#include <stdlib.h>

int n = 100;

/*@ ensures n < 0;
 @*/
int testV3();

int testV3()
{
	int *p = (int*) malloc(sizeof(int));
	// ...
	while (n >= 0)
	{
		int x = *p;
		int *a = p;
		if (n == 0)
		{
			//@ assert \valid(p);
			free(a);
			//@ assert !\valid(p);
		}
		n--;
	}
	return n;
}

/*@ ensures n < 0;
 @*/
int testV2();

int testV2()
{
	int *p = (int*) malloc(sizeof(int));
	// ...
	while (n >= 0)
	{
		int x = *p;
		if (n == 0)
		{
			free(p);
		}
		n--;
	}
	return n;
}

/*@ ensures n < 0;
 @*/
int testV1();

int testV1()
{
	int *p = (int*) malloc(sizeof(int));
	// ...
	while (n >= 0)
	{
		int x = *p;
		if (n == 0)
		{
			p = 0;
		}
		n--;
	}
	return n;
}

int main()
{
	testV1();

	n = 100;
	testV2();

	n = 100;
	testV3();
	return n;
}
