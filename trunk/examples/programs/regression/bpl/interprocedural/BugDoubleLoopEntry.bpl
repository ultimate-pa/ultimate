//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 01.04.2012
 * 
 * Bug: We obtain two loop entrys but there is only one loop.
 *
 */


procedure encT() returns () {
	var x, y, z:int;
	
	havoc x;
	while(*) {
		havoc y;
		if (*) {	
		  return;
		}
		havoc z;
	}
}

