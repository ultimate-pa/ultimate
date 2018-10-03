extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int a = 5;
int x = 0;

int f(int b) {
	x = ++b;
	return x;
}

int main() {
	
	a = f(f(a++));
	
    if (a == x) {
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}


