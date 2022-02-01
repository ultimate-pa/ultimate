//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.3.2012
 * 
 * Since g may not be modified, ensures clause of proc can not hold.
 */

var g: int;

procedure proc() returns ();
ensures g==old(g)+1;




  
