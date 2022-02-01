int nondef(void);

void test_fun(int i)
{
    while (i < 255) {
        if (nondef()) {
            i = i + 1;
        } else {
            i = i + 2;
        }
    }
}
