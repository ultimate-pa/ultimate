/*
 * Author: hoenicke@informatik.uni-freiburg.de
 *
 * Translated from scan.c in tacas06data by hand.
 *
 */

var x : [int] int;
var i,j : int;

procedure main()
{
   i := 0;
   havoc j;

   while (x[i] != 0) {
      i := i + 1;
   }

   if (j >= 0 && j < i) {
      assert (x[j] != 0);
   }
}
