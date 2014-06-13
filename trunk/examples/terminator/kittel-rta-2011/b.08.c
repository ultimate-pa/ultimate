void assume(int);
int nondef(void);

void test_fun(int x, int tmp)
{
    while (x > 0) {
        tmp = nondef();
        if (nondef()) {
            assume (x == 2*tmp);
            assume (tmp - 1 >= 0);
            x = tmp;
        } else {
            assume (x == 2*tmp + 1);
            assume (tmp >= 0);
            x = x - 1;
        }
    }
}
