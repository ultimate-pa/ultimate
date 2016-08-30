extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    while (x >= 0) {
        y = 1;
        while (x > y) {
	    if(y <= 0) {
	       // replace assume
	       return x;
	    }
            y = 2*y;
        }
        x = x - 1;
    }
    return y;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
