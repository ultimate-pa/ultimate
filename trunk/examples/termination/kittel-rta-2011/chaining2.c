void test_fun(int x, int flag)
{
    while (x > 0) {
        if (flag > 0) {
            x = x + 1;
            flag = 0;
        } else {
            x = x - 3;
            flag = 1;
        }
    }
}
