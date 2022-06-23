//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 07.06.2022
 */

var x: int;

procedure setZero() returns()
modifies x;
{
  var i : int;
  i := 4;
  x := 0;
  x := x-2; // division + ultimate
}

procedure division() returns()
modifies x;
{
 var i : int;
 i := 6;
 i := x; // ultimate
 fork 3 setZero();
 x := 3;
 i := i/x; // ultimate + setZero
}

procedure ULTIMATE.start() returns()
modifies x;
{
 var i : int;
 i := x; // ---
 fork 1 division(); 
 i := x: // division + setZero
 i := x; // division + setZero
}
