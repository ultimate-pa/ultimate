// Test program for block encoding.
// Only x=1 should be relevant. 

void main(void) {
	
	int x=1;
	int c = 10;
	if (c==10) {
		c = 2;	
	}
	if (c==2){
		if(c == 2)
		{
			c = 4;
		}
		c = 3;
		if(c == 3)
		{
			c = 1;
		}	
	}

	if(x == 1) __VERIFIER_error();

}
