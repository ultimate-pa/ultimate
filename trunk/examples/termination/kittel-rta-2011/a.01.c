void test_fun(int x, int y)
{
    while (x > 0) {
        y = 0;
        while (y < x) {
            y = y + 1;
        }
        x = x - 1;
    }
}
