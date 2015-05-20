//#Terminating
// Bug with oldVars in supporting invariants. Switch of termination argument
// simplification to reproduce.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-05-20


int x = 300;
int y = 2;
int z = 5;

void foo() {
	while (x > 0) {
		x = x - y;
		x = x - z;
	}
}

void proc() {
	x++;
	y--;
	foo();
}

int main() {
	x++;
	y++;
	z--;
	proc();
	return 0;
}

