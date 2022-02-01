extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    int c = 0;
    if(x <= 0 || y <= 0) {
       // replace assume
       return x + y;
    }
    while (!(x == 0)) {
        if (x > y) {
            x = y;
        } else {
	    if(x <= 0) {
	       // replace assume
	       return x;
	    }
            x = x - 1;
        }
        c = c + 1;
    }
    return c;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
