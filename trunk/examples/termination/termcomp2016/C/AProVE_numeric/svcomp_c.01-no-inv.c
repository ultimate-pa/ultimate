extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int c = 0;
    while (x >= 0) {
        y = 1;
        while (x > y) {
            y = 2*y;
            c = c + 1;
        }
        x = x - 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
