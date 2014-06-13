int minus(int x, int y) {
    while (y != 0) {
        if (y > 0)  {
            y--;
            x--;
        } else  {
            y++;
            x++;
        }
    }
    return x;
}

int mdiv(int x, int y) {
    int res = 0;
    while (x >= y && y > 0) {
        x = minus(x,y);
        res = res + 1;
    }
    return res;
}
