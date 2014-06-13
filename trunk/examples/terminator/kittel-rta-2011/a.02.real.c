int nondef(void);

void test_fun(int l, int u)
{
    while (l < u) {
        if (nondef()) {
            l = (l + u + 2) / 2;
        } else {
            u = (l + u) / 2;
        }
    }
}
