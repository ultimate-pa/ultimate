extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y, int tmp)
{
    while (x > y) {
        tmp = x;
        x = y;
        y = tmp;
    }
    return tmp;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
