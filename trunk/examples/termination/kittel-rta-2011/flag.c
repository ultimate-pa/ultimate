void f(int x, int y)
{
    int flag = 1;
    while (flag) {
        flag = (x++ < y);
    }
}
