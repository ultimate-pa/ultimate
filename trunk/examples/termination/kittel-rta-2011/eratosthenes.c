#include <stdio.h>

#define N 1000

int main()
{
    int i, j, a[N+1];
    for (a[1] = 0, i = 2; i <= N; i++) {
        a[i] = 1;
    }
    for (i = 2; i <= N / 2; i++) {
        for (j = 2; j <= N / i; j++) {
            a[i*j] = 0;
        }
    }
    for (i = 1; i <= N; i++) {
        if (a[i]) printf("%4d", i);
    }
    printf ("\n");
    return 0;
}
