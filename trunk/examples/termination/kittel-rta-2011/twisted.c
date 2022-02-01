void f(int k, int l)
{
    int i = 0, j = 0;
L1: while (i < k) {
        i++;
        if (i % 2) {
            continue;
        }
        goto L2;
    }
L2: while (j < l) {
        j++;
        if (i % 2) {
            continue;
        }
        goto L1;
    }
}
