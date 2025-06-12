//#Safe
/*
 * We get the following error: AssertionError: LES unsolvable
 *
 * Author: Matthias Heizmann
 * Date: 2023-01-06
 * 
 */

var x, u, v : int;


procedure main() returns () 
modifies x,u,v;

{
  while(*)
  {
      u, v := v, u + x;
  }
}
