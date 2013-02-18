/*
 * Author: hoenicke@informatik.uni-freiburg.de
 *
 * Translated from loop1.c in tacas06data by hand.
 *
 */

var x : [int] int;
var i,j,n : int;

procedure main()
{
   havoc j;
   i := 0;
   while ( i < 100) {
      x[i] := i;
      i := i + 1;
   }

   if (0 <= j && j < 100) {
      assert (x[j] == j);
   }
}
