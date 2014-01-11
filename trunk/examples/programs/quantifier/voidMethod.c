//#Unsafe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012
int x = 0;

/*@
  @ assigns x;
  @*/
void inc();

void inc() {
	x++;

}

int ga();

void main() {
	inc();
	ga();
	int three = ga();
	//@ assert three == 3;
	//@ assert x != 1000;
	voidFunc();
	//@ assert x == 1000;
	int random = voidFunc();
	//@ assert x == 1000;
	// THE FOLLLOWING SHOULD FAIL!
	//@ assert random == 1000;
}

int ga() {
	return 3;
}

void voidFunc(void) {
	x = 1000;
	return x;
}
