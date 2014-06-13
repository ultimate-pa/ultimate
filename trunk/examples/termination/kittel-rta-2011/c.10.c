void assume(int);
int nondef(void);

void test_fun(int i, int j, int tmp)
{
    while (i - j >= 1) {
        tmp = nondef();
        assume (tmp >= 0);
        i = i - tmp;
        tmp = nondef();
        assume (tmp > 0);
        j = j + tmp;
    }
}
