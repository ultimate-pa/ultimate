void test_fun(int x, int y, int r)
{
    r = 1;
    while (y > 0) {
        r = r*x;
        y = y - 1;
    }
}
