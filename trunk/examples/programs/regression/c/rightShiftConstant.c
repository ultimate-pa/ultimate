// #Unsafe
/*
 * Test for right shift with constant, see https://github.com/ultimate-pa/ultimate/issues/642
 * 
 * Date: 2023-08-01
 * Author: Novak756
 *
 */

extern void __VERIFIER_error(void);
extern unsigned char __VERIFIER_nondet_uchar(void);

int main(){
	unsigned char uc = __VERIFIER_nondet_uchar();
	if((unsigned int) ((unsigned int)(((unsigned int)(((unsigned int) uc) + ((unsigned int)(((unsigned int) 4294967295) *  1)))) >> ((unsigned int) 2))) < (unsigned int)  8){
		__VERIFIER_error();
	}
    return 0;
}