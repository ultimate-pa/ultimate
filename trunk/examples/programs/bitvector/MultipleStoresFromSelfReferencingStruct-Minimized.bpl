//#Safe
/* Date: 2017-10-08
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



var mem : [bv32]bv16;
var p1 : bv32;
var p2 :bv32;
var input : bv32;
var output : bv32;





procedure ULTIMATE.start() returns (){


    assume input == 3bv32;
    assume mem[p1] == input[16:0] && mem[p2] == input[32:16];
    assume output == mem[p2] ++ mem[p1];
    assert output == 3bv32;
    return;
}

