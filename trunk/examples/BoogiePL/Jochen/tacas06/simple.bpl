/*
 * Author: hoenicke@informatik.uni-freiburg.de
 *
 * Translated from simple.c in tacas06data by hand.
 *
 */


procedure main()
{
   var x,y,z : [int] int;
   var from,to,i,j,k : int;
  
   havoc i;
   havoc k;

   assume(k >= 0 && k <= 100 && x[k] == 0);
   assume(i <= k);
   while (x[i] != 0) {
      i := i + 1;
   }

   assert (i <= 100 && x[k] == 0); // typo in c-program?  Should probably be:
   //assert (i <= 100 && x[i] == 0);
}
