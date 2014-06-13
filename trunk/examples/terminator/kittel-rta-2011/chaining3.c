void test_fun(int x)
{
    while (!(x == 0)) {
        if (x > 0) {
            x = -x + 1;
        } else {
            x = -x - 1;
        }
    }
}
