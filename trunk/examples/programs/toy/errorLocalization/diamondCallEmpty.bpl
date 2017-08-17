//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-07
 */

procedure main() {
	var x: int;
	if (x > 0) {
		call callee();
	} else {
		call callee();
	}
	assert(false);
}


procedure callee() returns ()
{
}
