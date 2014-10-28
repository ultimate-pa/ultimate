extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
    int a, b;

    if (a > 10) {
		if(a < 100){
			b = 1;
		} else {
			b = 2;
		}
	} else {
		if(a < 5){
			b = 3;
		} else {
			b = 4;
		}
	}
	
	if(b == 3){
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}
