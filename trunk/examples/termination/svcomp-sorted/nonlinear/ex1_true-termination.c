extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y, int r)
{
    r = 1;
    while (y > 0) {
        r = r*x;
        y = y - 1;
    }
    return r;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
