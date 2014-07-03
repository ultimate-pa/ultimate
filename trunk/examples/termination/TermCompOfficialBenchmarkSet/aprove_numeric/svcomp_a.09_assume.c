extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y, int z)
{
    if(y <= 0) {
    	// replace assume
    	return z;
    }
    while (x >= z) {
    	if(y <= 0) {
		// replace assume
		return z;
    	}
        z = z + y;
    }
    return z;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
