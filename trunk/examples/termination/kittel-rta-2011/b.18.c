void test_fun(int x, int y)
{
    while ((x > 0) && (y > 0)) {
        if (x > y) {
            while (x > 0) {
                x = x - 1;
            }
        } else {
            while (y > 0) {
                y = y - 1;
            }
        }
    }
}
