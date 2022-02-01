void assume(int);
int nondef(void);

void test_fun(int l, int u, int tmp)
{
    while (l < u) {
        if (nondef()) {
            tmp = nondef();
            assume (l + u - 2*tmp >= 0);
            assume (l + u - 2*tmp <= 1);
            l = tmp + 1;
        } else {
            tmp = nondef();
            assume (l + u - 2*tmp >= 0);
            assume (l + u - 2*tmp <= 1);
            u = tmp;
        }
    }
}
