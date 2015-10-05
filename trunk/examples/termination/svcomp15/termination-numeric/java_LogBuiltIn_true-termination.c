extern int __VERIFIER_nondet_int(void);

int mlog(int x) {

    int res = 0;

    while (x > 1) {

        x = x/2;
        res++;

    }

    return res;

}

int main() {
    return mlog(__VERIFIER_nondet_int());
}
