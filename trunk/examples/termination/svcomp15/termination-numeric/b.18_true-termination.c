extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    while ((x > 0) && (y > 0)) {
        if (x > y) {
            while (x > 0) {
                x = x - 1;
            }
        } else {
            while (y > 0) {
                y = y - 1;
            }
        }
    }
    return x + y;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
