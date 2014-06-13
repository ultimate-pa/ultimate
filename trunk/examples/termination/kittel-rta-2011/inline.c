int min(int i, int j)
{
    if (i < j) {
        return i;
    } else {
        return j;
    }
}

void test(int i, int j)
{
    while (i > j) {
        i = min(i, j);
    }
}
