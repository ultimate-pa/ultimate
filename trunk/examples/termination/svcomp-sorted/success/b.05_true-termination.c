extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int tmp)
{
    tmp = __VERIFIER_nondet_int();
    while ((x > 0) && (x == 2*tmp)) {
        x = x - 1;
        tmp = __VERIFIER_nondet_int();
    }
    return x;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
