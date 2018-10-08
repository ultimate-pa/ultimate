extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
    int a, b, c, d, e, f;
	a = 2;
	b = 2;
    c = 2;
    d = 2;
    e = 2;
    f = 2;
	
    while (a > 0) {
		a--;
	} 
	
	while (b > 0){
		b--;
		while(c > 0){
			c--;
		}
	}
	
	for(;d>0;d--){
		e--;
	}
	
	do{
		f--;
	} while(f>0);
	
	
	if(a == 0){
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}
