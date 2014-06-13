void assume(int);

void test_fun(int x, int y)
{
    assume (x > 0);
    assume (y > 0);
    while (!(x == 0)) {
        if (x > y) {
            x = y;
        } else {
            assume (x > 0);
            x = x - 1;
        }
    }
}
