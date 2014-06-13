void knapsack(int size[], int val[], int N, int cost[], int best[], int M)
{
    int i, j;
    for (j = 1; j <= N; j++) {
        for (i = 1; i <= M; i++) {
            if (i >= size[j]) {
                if (cost[i] < cost[i - size[j]] + val[j]) {
                    cost[i] = cost[i - size[j]] + val[j];
                    best[i] = j;
                }
            }
        }
    }
}
