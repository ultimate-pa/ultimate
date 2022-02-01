int func(int n)
{
    return n << n;
}

int f(int n)
{
    int c;
    int res = 1;
    for (c = 0; c < func(n); ++c) {
        res = res * c;
    }
    return res;
}
