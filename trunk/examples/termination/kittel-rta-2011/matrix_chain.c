#include <limits.h>

void matrix_chain(int *cost[], int *best[], int r[], int N)
{
    int i, j, k;
    int t;
    for (i = 1; i <= N; i++) {
        for (j = 2; j < N; j++) {
            cost[i][j] = INT_MAX;
        }
    }
    for (i = 1; i <= N; i++) {
        cost[i][i] = 0;
    }
    for (j = 1; j < N; j++) {
        for (i = 1; i <= N - j; i++) {
            for (k = i+1; k <= i + j; k++) {
                t = cost[i][k-1] + cost[k][i+j] + r[i]*r[k]*r[i+j+1];
                if (t < cost[i][i+j]) {
                    cost[i][i+j] = t;
                    best[i][i+j] = k;
                }
            }
        }
    }
}
