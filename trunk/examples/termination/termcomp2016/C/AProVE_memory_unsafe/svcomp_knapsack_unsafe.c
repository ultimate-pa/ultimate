extern int __VERIFIER_nondet_int(void);

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

int main() {
  int *size;
  int *val;
  int N = __VERIFIER_nondet_int();
  int *cost;
  int *best;
  int M = __VERIFIER_nondet_int();
  knapsack(size, val, N, cost, best, M);
  return 0;
}
