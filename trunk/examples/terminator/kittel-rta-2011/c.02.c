void test_fun(int x, int y)
{
    while (x >= 0) {
        x = x + 1;
        y = 1;
        while (x > y) {
            y = y + 1;
        }
        x = x - 2;
    }
}
