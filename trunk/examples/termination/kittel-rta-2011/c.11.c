int nondef(void);

void test_fun(int x, int y, int flag)
{
    flag = 1;
    while (flag > 0) {
        if (x >= 0) {
            x = x - 1;
            y = nondef();
        } else {
            if (y >= 0) {
                y = y - 1;
            } else {
                flag = 0;
            }
        }
    }
}
