//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 07.06.2022
 */

var x: int;
var y: int;

procedure whileloop() returns()
modifies x,y;
{
  var i : int;
  i := 2;
  y := 3;
  x := y - (x * i);
  fork 3 whileloop();
  fork 4 ifstatement();
  while (i < 5) {
     i := i + 1;
     x := i;
  }
  x := x-2;
}

procedure ifstatement() returns()
modifies x,y;
{
 var i : int;
 x := 3;
 if (i < 5) {
     i := i + 1;
     y := x;
 } else {
     x := i;
     i := i - 1;
 }
 i := i/x;
}

procedure ULTIMATE.start() returns()
modifies x,y;
{
 y := 2;
 fork 1 whileloop();
 fork 2 ifstatement();
 x := y;
}
