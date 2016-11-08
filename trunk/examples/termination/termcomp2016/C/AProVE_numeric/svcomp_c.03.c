extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y, int z)
{
    int c = 0;
    while (x < y) {
        if (x < z) {
            x = x + 1;
        } else {
            z = z + 1;
        }
        c = c + 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}


