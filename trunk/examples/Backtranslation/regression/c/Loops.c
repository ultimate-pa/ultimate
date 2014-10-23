extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
    int a, b;
	a = 12;
	b = 0;
	
    while (a > 10) {
		a--;
	} 
	
	while (a > 5){
		b++;
		while(a > 7){
			a--;
		}
		a--;
	}
	
	for(;a>0;a--){
		b++;
	}
	
	do{
		b--;
	} while(b>0);
	
	
	if(b == 0){
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}
