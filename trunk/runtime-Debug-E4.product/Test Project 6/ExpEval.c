extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
    int a=0;
	int b=0;
	
	a = a++ + b++ + ++a + ++b;
	b = a-- - b-- - --a - --b;
	
	
	if(b == 0){
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}