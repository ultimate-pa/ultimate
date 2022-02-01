void diff(int *A, int Alen, int *B, int Blen, int *D)
{
    int k = 0;
    int i = 0;
    int l1 = Alen;
    int l2 = Blen;
    int found;

    while (i < l1) {
        int j = 0;
        found = 0;
        while (j < l2 && !found) {
            if(A[i] == B[j]) {
                found = 1;
            } else {
                j++;
            }
        }
        if (!found) {
            D[k] = A[i];
            k++;
        }
        i++;
    }
}
