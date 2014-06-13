int nondef(void);

void mmain() {
    int x = nondef();
    int y = nondef();

    while ((x > y) && (y > 2)) {
        x++;
        y = 2*y;
    }
}
