//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-06
// 
// Similar to `NonterminatingForLoopSafe.c` but
// (surprisingly) the WitnessPrinter does not crash
// (with a NullPointerException).
// However, the log shows the following error message.
//
// WARN  L320   BoogieBacktranslator]: Removing null node from list of ATEs: ATE  program state null

int main() {
	int i = 0;
	for (;;) {
		i++;
		//@ assert i != 5;
	}
}

