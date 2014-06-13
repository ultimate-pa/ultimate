int le(int x, int y) {
    if (x > 0 && y > 0) {
        return le(x-1, y-1);
    } else {
        return (x == 0);
    }
}
