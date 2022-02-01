//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-11
// Obtained from Markus Lindenmann's enum example.
// Local enum does not have to be initialized with zero.


int main() {
	enum BOOLEAN {
		false, true
	} end_flag;
	enum BOOLEAN match_flag;
	int x = 23;
	if (match_flag == false) {
		x = 42;
	}
	end_flag = true;
	//@ assert x == 42;
}
