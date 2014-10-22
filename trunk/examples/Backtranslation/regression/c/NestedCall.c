extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void printf(char *format);
void assert_fail(void);

int main() {
    int a = 5;
	
	a = f(f(a++));
	
    if (a != 7) {
        printf("ERROR\n");
        assert_fail();
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}

int f(int a) {
	return a++;
}
