#include <limits.h>

void opt_tree(int *cost[], int f[], int *best[], int N)
{
    int i, j, k;
    int t;
    for (i = 1; i <= N; i++) {
        for (j = i + 1; j <= N + 1; j++) {
            cost[i][j] = INT_MAX;
        }
    }
    for (i = 1; i <= N; i++) {
        cost[i][i] = f[i];
    }
    for (i = 1; i <= N + 1; i++) {
        cost[i][i-1] = 0;
    }
    for (j = 1; j <= N - 1; j++) {
        for (i = 1; i <= N - j; i++) {
            for (k = i; k <= i + j; k++) {
                t = cost[i][k-1] + cost[k+1][i+j];
                if (t < cost[i][i+j]) {
                    cost[i][i+j] = t;
                    best[i][i+j] = k;
                }
            }
            for (k = i; k <= i + j; cost[i][i+j] += f[k++]) ;
        }
    }
}
