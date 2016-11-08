extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int c = 0;
    while (!(x == y)) {
        if (x > y) {
            y = y + 1;
        } else {
            x = x + 1;
        }
        c = c + 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
