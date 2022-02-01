int nondef(void);

void mmain() {
    int x = nondef();
    int y = nondef();
    int z;
    int res = 0;

    while (y > 0) {

        z = x;
        x = y-1;
        y = z;
        res++;

    }

    res = res + x;
}
