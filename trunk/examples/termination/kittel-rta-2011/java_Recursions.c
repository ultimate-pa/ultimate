void rec0(int, int);
void rec1(int, int, int);
void rec2(int, int, int, int);
void rec3(int, int, int, int, int);
void rec4(int, int);

void mmain(int n) {
    int i;
    for (i = 0; i < n; i++)
        rec0(0, n);
}

void rec0(int i, int stop) {
    if (i <= stop) {
        rec1(0, 2*i, i);
        rec0(i+1, stop);
    }
}

void rec1(int j, int stop, int i) {
    if (j <= stop) {
        rec2(i+j, 0, i, j);
        rec1(j+1, stop, i);
    }
}

void rec2(int k, int stop, int i, int j) {
    if (k >= stop) {
        rec3(0, 2*i + 3*j + 4*k, i, j ,k);
        rec2(k-1, stop, i, j);
    }
}

void rec3(int l, int stop, int i, int j, int k) {
    if (l <= stop) {
        rec4(1000*i+100*j+10*k+l, 0);
        rec3(l+1, stop, i, j, k);
    }
}

void rec4(int m, int stop) {
    if (m >= stop)
        rec4(m-1, stop);
}
