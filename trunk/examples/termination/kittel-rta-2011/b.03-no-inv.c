void assume(int);

void test_fun(int x, int y)
{
    assume (x > 0);
    while (x > y) {
        y = y + x;
    }
}
