#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

// Returns the length of the longest increasing subsequence.
// Note that this is looking for the longest strictly increasing subsequence.

int lis(int* a, int N)
{
    int *best, *prev, i, j, max = 0;
    best = (int*) malloc(sizeof(int) * N);
    prev = (int*) malloc(sizeof(int) * N);

    for (i = 0; i < N; i++)
        best[i] = 1, prev[i] = i;

    for (i = 1; i < N; i++)
        for (j = 0; j < i; j++)
            if (a[i] > a[j] && best[i] < best[j] + 1)
                best[i] = best[j] + 1, prev[i] = j;  // prev[] is for backtracking the subsequence

    for (i = 0; i < N; i++)
        if (max < best[i])
            max = best[i];

    free(best);
    free(prev);

    return max;
}

int main() {
  int *a;
  int N = __VERIFIER_nondet_int();
  return lis(a, N);
}
