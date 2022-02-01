//#Unsafe

/*
 * This regression test demonstrates the need to include cutoff events in the co-relation
 * in order to make Petri net LBE sound:
 * Since the assignment "x:=x+1" is a cutoff event (assuming "y:=0" is expanded earlier),
 * excluding cutoff events means "x:=0" commutes with all co-enabled events,
 * leading to the unsound composition of "x:=0" with "x:=2*x".
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 15. 01. 2020
 */

var x : int;
var y : int;

procedure ULTIMATE.start() returns ()
modifies x, y;
{
   fork 1 Thread1();

   x := 0;
   x := 2 * x;

   join 1;
   assert x != 2;
}

procedure Thread1() returns ()
modifies x, y;
{
   if (*) {
      while (*) { assume true; } // prevent LBE from applying choice rule
      y := 0;
   } else {
      while (*) { assume true; } // prevent LBE from applying choice rule
      x := x+1;
   }
}
