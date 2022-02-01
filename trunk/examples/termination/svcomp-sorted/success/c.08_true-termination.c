extern int __VERIFIER_nondet_int(void);

int test_fun(int i, int j)
{
    int c = 0;
    while (i >= 0) {
        j = 0;
        while (j <= i - 1) {
            j = j + 1;
            c = c + 1;
        }
        i = i - 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
