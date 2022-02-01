void test_fun(int i, int j)
{
    while (i >= 0) {
        j = 0;
        while (j <= i - 1) {
            j = j + 1;
        }
        i = i - 1;
    }
}
