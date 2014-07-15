//#Safe
/*
 * At the moment we are unable to find a the loop invariant x==y,
 * because we obtain the interpolants
 * x==0 /\ y==0
 * x==1 /\ y==1
 * x==2 /\ y==2
 * ....
 * If we replace the integer literal "0" by a variable of constant 
 * "zero" we obtain the interpolants x==y.
 * 
 * Date: 14.10.2013
 * Author: heizmann@informatik.uni-freiburg.de and Betim Musa
 *
 */

procedure main()
{
  var x, y, zero, one, hundred: int;
  
  x := 0;
  y := 0;

  while (*) {
    x := x + 1;
    y := y + 1;
  }

  assert(x != 100 || y == 100);

} 
