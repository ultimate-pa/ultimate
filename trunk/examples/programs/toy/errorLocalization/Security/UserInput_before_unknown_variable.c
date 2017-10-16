// Securtiy error according to vadim's program
// But not according to our definition

#include<stdio.h>

void __VERIFIER_error();
int get_a(void);
int user_input(void);


void main(void) {
	int user_value = user_input();
	int a = get_a();

	if(user_value == a){
		__VERIFIER_error();
	}
}
