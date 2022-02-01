int nondef(void);

void test_fun(int x, int y)
{
    while ((x > 0) && (y > 0)) {
        if (nondef()) {
            x = x - 1;
            y = nondef();
        } else {
            y = y - 1;
        }
    }
}
