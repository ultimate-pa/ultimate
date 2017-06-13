extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
	int i;
    int a[6] = {1,2,3,4,5,6};
	a[5] = 10;

	for ( i = 0; i < 5; i++ )
	{
		a[i] = 0;
	}

    if (a[5] == 10) {
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}