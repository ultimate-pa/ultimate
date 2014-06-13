void assume(int);
int nondef(void);

void test_fun(int x, int debug, int tmp)
{
    debug = 0;
    while (x < 255) {
        tmp = nondef();
        if (nondef()) {
            assume (x == 2*tmp + 1);
            x = x - 1;
        } else {
            assume (x == 2*tmp);
            x = x + 2;
        }
        assume (debug == 0);
        if (!(debug == 0)) {
            x = 0;
        } else {
            
        }
    }
}
