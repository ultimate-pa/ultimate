void selection(int a[], int N)
{
    int i, j, min, t;
    for (i = 1; i < N; i++) {
        min = i;
        for (j = i+1; j <= N; ++j) {
            if (a[j] < a[min]) {
                min = j;
            }            
        }
        t = a[min];
        a[min] = a[i];
        a[i] = t;
    }
}
