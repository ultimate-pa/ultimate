int nondef(void);

void test_fun(int x, int y)
{
    x = nondef();
    y = nondef();
    while ((x > 0) && (y > 0)) {
        if (nondef()) {
            x = x - 1;
            y = y + 1;
        } else {
            y = y - 1;
        }
    }
}
