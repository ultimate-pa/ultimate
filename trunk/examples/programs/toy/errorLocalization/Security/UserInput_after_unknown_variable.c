// Securtiy error according to vadim's program
// Also according to our definition.

#include<stdlib.h>

void __VERIFIER_error();
int get_a(void);
int user_input(void);


void main(void) {
	int a = get_a();
	int user_value = user_input();

	if(user_value == a){
		__VERIFIER_error();
	}
}
