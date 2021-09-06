//#Safe
/*
 * The update in this loop is actually not linear because of
 * the subterm (x % 4).
 * Since x is not modified in the loop, we however consider
 * the subterm (x % 4) as a variable of the loop and hence
 * consider the update of i as a linear update.
 * 
 * Author: Matthias Heizmann
 * Date: 2021-04-29
 * 
 */

var i, x : int;
var B : bool;

procedure main() returns ()
modifies i,x,B;
{

  i := 0;
  while(B)
  {
      i := i + 7 * (x % 4);
      havoc B;
  }
  assert (i >= 0);
}


