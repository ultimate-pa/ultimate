//#terminating
/*
 * Terminating program that has no linear lexicographic ranking function.
 * The program chooses nondeterministically the variable x or y and assigns to
 * it the result of   minimum(x,y)-1
 * The term   minimum(x,y)  is a ranking function for this program.
 * 
 * Amir Ben-Amram (TelAviv) showed me this program when we met in Perpignan at
 * SAS 2010.
 *
 * Date: 1.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y: int;

procedure main()
modifies x, y;
{
  while (x>0 && y>0) {
    if (*) {
      if (x<y) {
        y := x - 1;
      } else {
        y := y - 1;
      }
      havoc x;
    } else {
      if (x<y) {
        x := x - 1;
      } else {
        x := y - 1;
      }
      havoc y;
    }
  }
}