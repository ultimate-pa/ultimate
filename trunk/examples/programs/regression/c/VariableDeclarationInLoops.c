//#Unsafe
// Date: 14.01.2013

int test(void);

int main(void)
{
	int y;
	int x = 5;
	while(x>0) {
		int z;
		y = z;
		// assert that does not hold
		//@assert y != 0;
	}
	x = test();
}

int test() {
	MY_LABEL:;
	int x;
	if (x != 0) {
		goto MY_LABEL;
	}
	// assert that holds
	//@assert x == 0;
}
