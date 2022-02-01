void test_fun(int i, int j, int k, int tmp)
{
    while ((i <= 100) && (j <= k)) {
        tmp = i;
        i = j;
        j = tmp + 1;
        k = k - 1;
    }
}
