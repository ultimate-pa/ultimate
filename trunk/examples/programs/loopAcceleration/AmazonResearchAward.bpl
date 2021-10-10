//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-01-07
 * 
 * Simplified version of 2020TACAS-Frohn-NonDec.bpl
 * I used this example in the proposal for an Amazon Research Award.
 */

  var a, b : int;


procedure main() returns () 
modifies a,b;

{
  while(a > 0)
  {
      a := a - 1;
      b := b + 1;
  }
}
