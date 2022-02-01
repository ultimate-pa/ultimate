int average(int x, int y) {
    if (x > 0) {
        return average(x-1, y+1);
    } else if (y > 2) {
        return 1 + average(x+1, y-2);
    } else {
        return 1;
    }
}
