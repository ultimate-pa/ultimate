extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int f(int b) {
	return ++b;
}


int main() {
    int a = 5;
	
	a = f(f(a++));
	
    if (a != 8) {
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}

