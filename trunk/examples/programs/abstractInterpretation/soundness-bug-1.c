/*
 * Inserting unsound transition 
 *
 */
void __VERIFIER_assert(int cond) {
    ERROR: __VERIFIER_error();
}

int base2flt(int e ) 
{  
    while (1) {
		if (e >= 127) {
			break;
		} 
		e = e + 1;
	}
	return 0;
}

void main() 
{
	base2flt(0);
    __VERIFIER_assert(0);
}
