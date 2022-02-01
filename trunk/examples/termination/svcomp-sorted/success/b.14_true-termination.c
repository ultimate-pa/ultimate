extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int c = 0;
    while ((x == y) && (x > 0)) {
        while (y > 0) {
            x = x - 1;
            y = y - 1;
            c = c + 1;
        }
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
