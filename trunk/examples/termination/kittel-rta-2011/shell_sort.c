void assume(int);

void shell(int a[], int N)
{
    int i, j, h, v;
    int tmp = N / 9;
    for (h = 1; h < tmp; assume(h > 0), h = 3*h + 1);
    for (; h > 0; h /= 3) {
        for (i = h + 1; i <= N; assume(h > 0), i += h) {
            v = a[i];
            j = i;
            while (h > 0 && j > h && a[j - h] > v) {
                a[j] = a[j - h];
                assume(h > 0);
                j -= h;
            }
            a[j] = v;
        }
    }
}
