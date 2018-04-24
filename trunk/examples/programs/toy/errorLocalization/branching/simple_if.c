// Test program for block encoding.
// Only x=1 should be relevant. 
// simple if example.

void main(void) {
	
	int x = 1;
	int c = 10;

	if (c==10) {
		c = 2;	
	}
	if(x == 1) __VERIFIER_error();
}
