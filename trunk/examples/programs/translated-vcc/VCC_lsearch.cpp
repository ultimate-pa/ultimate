#include "vcc.h"
#include <limits.h>

int lsearch(int elt, int *ar, unsigned int sz)
  requires(0 <= sz)
  requires(sz < INT_MAX / sizeof(int))
  requires( wrapped( as_array( ar, sz ) ) )
  ensures(result >= 0 ==> ar[result] == elt)
  ensures(result < 0 ==> forall(int i; 0 <= i && i < (int)sz ==> ar[i] != elt))
{
	int i;
    for (i = 0; i < (int)sz; i++)
      invariant(0 <= i && i <= (int)sz)
      invariant(forall(int j; 0 <= j && j < i ==> ar[j] != elt))
    {
        if (ar[i] == elt) return i;
    }

    return -1;
}
