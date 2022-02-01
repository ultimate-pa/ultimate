int nondef(void);

void mmain() {
    int x = nondef();
    int y = nondef();
    int z = y;
    int res = 0;

    while (z > 0 && (y == 0 || (y > 0 && x > 0))) {
        if (y == 0) {
            res++;
            y = z;
        }
        else {
            x--;
            y--;
        }
    }
}
