void test_fun(int x, int y)
{
    while (x >= 0) {
        y = 1;
        while (x > y) {
            y = 2*y;
        }
        x = x - 1;
    }
}
