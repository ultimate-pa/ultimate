//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 07.06.2022
 */

var x: int;

procedure setZero() returns()
modifies x;
{
  var l : int;
  l := 4;
  x := 0;
  x := x-2; // division + ultimate 
}

procedure division() returns()
modifies x;
{
 var k : int;
 k := 6;
 k := x; // ultimate 
 fork 3 setZero();
 x := 3;
 k := k/x; // ultimate + setZero
}

procedure ULTIMATE.start() returns()
modifies x;
{
 var i : int;
 var j : int;
 i := 0;
 x := 0;
 while(i < 3) {
   i := i + 1;
   x := x + 1;
 }
 i := x; // ---
 fork 1 division(); 
 j := x; // division + setZero
}
