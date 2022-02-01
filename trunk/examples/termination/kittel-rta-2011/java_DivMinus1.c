int mdiv(int x, int y) {
    int res = 0;
    while (x >= y && y > 0) {
        x = x-y;
        res = res + 1;
    }
    return res;
}
