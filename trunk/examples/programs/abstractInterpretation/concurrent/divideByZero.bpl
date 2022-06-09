//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 07.06.2022
 */

var x: int;

procedure setZero() returns()
modifies x;
{
  x := 0;
}

procedure division() returns()
modifies x;
{
 var i : int;
 i := 4;
 x := 2;
 i := i/x;
}

procedure ULTIMATE.start() returns()
modifies x;
{
 fork 1 division();
 fork 2 setZero();
}
