//#Terminating
// Bug with oldVars in supporting invariants. Switch of termination argument
// simplification to reproduce.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-05-20


int x = 300;
int y = 2;

void proc() {
	y--;
	while (x > 0) {
		x = x - y;
	}
}

int main() {
	proc();
	return 0;
}

