//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-08
// 
// We fail to determine the enum value because of 
// the conditional operator.

enum
{
  wuhan = 0,
  alpha = 1,
  delta = 2 * alpha,
  omicron = alpha ? 3 * delta : 4 * alpha,
};

int main() {
	if (omicron != 6) {
		//@ assert \false;
	}
	return 0;
}
