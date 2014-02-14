//#Unsafe
/*
 * Bug in sequential composition in r6184
 * Date: 09.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() {
	 var c : int ;
	 var e : int ;
	 var d : int ;
	if (false) {
	} else {
		e := e + 1;
		d := 0;
	}
	e := e;
	c := e;
	assert (false);
}
