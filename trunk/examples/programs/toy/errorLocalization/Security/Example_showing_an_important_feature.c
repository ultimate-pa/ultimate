// Altough it seems like there is a check (validation) on the value
// of the variable y but the algorithm still detects
// the presence of an unvalidated input.
// 
// This example helps bring home an important property of
// unvalidated inputs in a program. Input validation is about
// validating that the input value cannot directly control the
// reachability of the error state.
 

int get_from_user(void);

void main(void) {
	
	int x = 1;
	int y = get_from_user(); // Unvalidated Input

	if (y < 10) {
		y++;	
	} else {
		x = 2;	
	}

	if(x == 1) __VERIFIER_error();

}
