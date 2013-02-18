/*
 * Author: hoenicke@informatik.uni-freiburg.de
 *
 * Translated from loop1.c in tacas06data by hand.
 * Added loop invariant.
 *
 */

procedure main()
{
   var x : [int] int;
   var i,j,n : int;

   havoc j;
   i := 0;
   while ( i < 100)
      invariant (forall y : int :: 0 <= y && y < i ==> x[y] == y);
   {
      x[i] := i;
      i := i + 1;
   }

   if (0 <= j && j < 100) {
      assert (x[j] == j);
   }
}
