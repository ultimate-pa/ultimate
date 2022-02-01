int nondef(void);

void test_fun(int x, int tmp)
{
    tmp = nondef();
    while ((x > 0) && (x == 2*tmp)) {
        x = x - 1;
        tmp = nondef();
    }
}
