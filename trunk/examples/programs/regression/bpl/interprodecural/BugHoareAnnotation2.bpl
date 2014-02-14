//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 02.05.2012
 * 
 * Modified Version of Jemeri and Vincents encT_TRE_with_Boogie_Specs-Light.bpl
 * example. Revealed bug in revision 5938. 
 * Computed Hoare annotation is not inductive if abstractions are minimized.
 *
 */

procedure main() returns ()
{
	call foo();
	call foo();
}


procedure foo() returns ()
{
	var ret:bool;
 	call ret := isOne();
	assert ret;
}

procedure isOne() returns (ret : bool)
{
	if (*) {
		ret := true;
	} else {
		ret := false;
	}
}