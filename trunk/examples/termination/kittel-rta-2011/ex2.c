void test_fun(int x, int y, int z, int flag)
{
    flag = 1;
    while ((y < z) && (flag > 0)) {
        if ((y > 0) && (x > 1)) {
            y = x*y;
        } else {
            if ((y > 0) && (x < -1)) {
                y = -x*y;
            } else {
                flag = 0;
            }
        }
    }
}
