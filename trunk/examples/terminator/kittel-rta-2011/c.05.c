void assume(int);
int nondef(void);

void test_fun(int x, int y)
{
    assume (x > 0);
    assume (y > 0);
    while (!(x == y)) {
        if (x > y) {
            assume (x > 0);
            assume (y > 0);
            x = x - y;
        } else {
            assume (x > 0);
            assume (y > 0);
            y = y - x;
        }
    }
}
