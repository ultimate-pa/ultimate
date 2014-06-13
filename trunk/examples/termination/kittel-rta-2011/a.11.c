int nondef(void);

void test_fun(int x, int y, int z)
{
    while (x > y) {
        if (x > z) {
            if (nondef()) {
                y = y + 1;
            } else {
                z = z + 1;
            }
        } else {
            x = x - 1;
        }
    }
}
