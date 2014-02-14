//#Safe
// Author: wisserts@informatik.uni-freiburg.de
// Date: 03.05.2013
// Bug in interprocedural sequential composition.

int proc() {
	return 21;
}

int main() {
	int k = proc();
	//@ assert k == 21;
}
