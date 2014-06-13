int plus(int x, int y) {
    if (y > 0) {
        return 1 + plus(x, y-1);
    } else if (x > 0) {
        return 1 + plus(x-1, y);
    } else {
        return 0;
    }
}

int times(int x, int y) {
    if (y == 0)
        return 0;
    if (y > 0)
        return plus(times(x, y - 1), x);
    return 0;
}
