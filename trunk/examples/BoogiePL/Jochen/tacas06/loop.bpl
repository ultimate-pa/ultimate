/*
 * Author: hoenicke@informatik.uni-freiburg.de
 *
 * Translated from loop.c in tacas06data by hand.
 *
 */

var x : [int] int;
var i,j,n : int;

procedure main()
{
   i := 0;
   while ( i < n) {
      x[i] := 0;
      i := i + 1;
   }

   if (0 <= j && j < n) {
      assert (x[j] == 0);
   }
}
