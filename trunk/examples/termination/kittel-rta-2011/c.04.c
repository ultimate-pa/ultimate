void assume(int);
int nondef(void);

void test_fun(int x, int y, int z)
{
    if (y > 0) {
        while ((x < y) && (y < z)) {
            if (nondef()) {
                assume (y > 0);
                x = x + y;
            } else {
                assume (y > 0);
                z = x - y;
            }
        }
    } else {
        
    }
}
