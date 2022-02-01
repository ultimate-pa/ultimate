void assume(int);

void test_fun(int x, int y, int z)
{
    assume (y > 0);
    while (x >= z) {
        assume (y > 0);
        z = z + y;
    }
}
