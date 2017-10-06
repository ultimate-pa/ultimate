//#Safe
/* Date: 2017-10-05
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Example where we need "multiple stores" in our partial quantifier
 * elimination for arrays.
 * 
 */
var p1 : int;
var oldmem : [int]int;
var p2 : int;
var mem : [int]int;

procedure ULTIMATE.start() returns ()
modifies mem;
{
  assume p2 != p1;
  
  assume (mem == oldmem[p1 := 23]);
  assume (mem == oldmem[p2 := 42]);

  assert mem[p2] == 42 && mem[p1] == 23;
}
