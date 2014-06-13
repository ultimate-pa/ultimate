int nondef(void);

void test_fun(int x, int y, int z)
{
    if (y > 0) {
        while ((x < y) && (y < z)) {
            if (nondef()) {
                x = x + y;
            } else {
                z = x - y;
            }
        }
    } else {
        
    }
}
