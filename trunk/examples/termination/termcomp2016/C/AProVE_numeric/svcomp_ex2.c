extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y, int z, int flag)
{
    int c = 0;
    flag = 1;
    while ((y < z) && (flag > 0)) {
        if ((y > 0) && (x > 1)) {
            y = x*y;
        } else {
            if ((y > 0) && (x < -1)) {
                y = -x*y;
            } else {
                flag = 0;
            }
        }
        c = c + 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
