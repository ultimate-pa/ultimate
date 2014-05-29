//#Safe
/* 
 * Bug: old(g) should be translated to g for procedures that do not
 * modify g.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 5.10.2013
 * 
 */

var g: int;

procedure ULTIMATE.start();
modifies g;

implementation ULTIMATE.start()
{
  call doNotModifyG();
}

procedure doNotModifyG() returns ();
ensures g == old(g);

implementation doNotModifyG() returns ()
{
  var i:int;
  i := i+1;
}
 
