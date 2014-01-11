//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 01.04.2012
 * 
 * Current implmentation has no edge from callees init to exit
 */

procedure caller()
{
        call callee();
	assert(false);
}


procedure callee() returns ()
{
}
