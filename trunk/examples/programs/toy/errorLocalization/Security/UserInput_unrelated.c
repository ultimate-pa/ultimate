// No security error
// Also no error according to our definition

#include<stdlib.h>

void __VERIFIER_error();
int get_a(void);
int user_input(void);


void main(void){
	int user_value = user_input();
	int a = get_a();

	if(!a){
		__VERIFIER_error();
	}
}
