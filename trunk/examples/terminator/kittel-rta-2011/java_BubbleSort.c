void sort(int *x, int n) {
    int pass;
    int i;
    for (pass=1; pass < n; pass++)  // count how many times
        // This next loop becomes shorter and shorter
        for (i=0; i < n - pass; i++)
            if (x[i] > x[i+1]) {
                // exchange elements
                int temp = x[i]; x[i] = x[i+1];  x[i+1] = temp;
            }
}
