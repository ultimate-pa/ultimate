// #Safe
// 
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2019-08-21

procedure ULTIMATE.start() returns () {
	assert myIncrement(0) == 1;
}

function myIncrement(in : int) : int {
	in + 1
}
