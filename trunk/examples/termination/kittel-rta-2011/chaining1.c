void assume(int);
int nondef(void);

void test_fun(int x, int tmp)
{
    while (x > 0) {
        tmp = nondef();
        if (nondef()) {
            assume (x == 2*tmp);
            x = x + 1;
        } else {
            assume (x == 2*tmp + 1);
            x = x - 3;
        }
    }
}
