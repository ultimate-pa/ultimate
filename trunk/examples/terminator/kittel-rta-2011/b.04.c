void test_fun(int x, int y, int tmp)
{
    while (x > y) {
        tmp = x;
        x = y;
        y = tmp;
    }
}
