#include "vcc.h"

int* sort(int* x, unsigned int l)
requires(l >= 1)
requires(is_array(x,l))
writes(array_range(x,l))
ensures(forall(unsigned int i, j; (((i < j) && (j < l)) ==> (x[i] <= x[j]))))
{
	unsigned int i = l - 1;
	unsigned int j;
	int temp;
	while (0 < i)
		// Valid range
		invariant(i >= 0 && i < l)
		// Element x[i+1] is greatest element in [0,i+1]
		invariant(forall(unsigned int m; ((m <= i+1) && (i+1 < l)) ==> (x[m] <= x[i+1])))
		// Element x[i+1] is least element in [i+1,l)
		invariant(forall(unsigned int o; ((i+1 <= o) && (o < l)) ==> (x[i+1] <= x[o])))
		// Elements above i are sorted
		invariant(forall(unsigned int n,m; ((n > i) && (n < m) && (m < l)) ==> (x[n] <= x[m])))
	{
		j = 0;
		while (j < i)
			// Valid range
			invariant(j >= 0 && j <= i)
			// x[j] is greatest element
			invariant(forall(unsigned int k; ((k < j) ==> (x[k] <= x[j]))))
			// Elements above i are sorted
			invariant(forall(unsigned int n,m; ((n > i) && (n < m) && (m < l)) ==> (x[n] <= x[m])))
			// all elements below i+1 are less than x[i+1] if i+1 is in range
			invariant(forall(unsigned int p; ((p <= i) && (i+1 < l)) ==> (x[p] <= x[i+1])))
		{
			if (x[j+1] < x[j])
			{
				temp = x[j];
				x[j] = x[j+1];
				x[j+1] = temp;
			}
			j = j + 1;
			//assert(false);
		}
		//assert(forall(unsigned int n; ((n >= i) ==> (x[i] <= x[n]))));
		//assert(forall(unsigned int n; ((n < i) ==> (x[n] <= x[i]))));
		i = i - 1;
		//assert(false);
	}
	//assert(false);
	return x;
}