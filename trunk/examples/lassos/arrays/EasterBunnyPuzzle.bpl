//#rTermination
/* The array a models a street with infinitely many farmhouses.
 * Each farmhouse has a finite number of eggs.
 * Because of the zombie apocalypse no new eggs can be produced.
 * 
 * The array a maps house numbers to the number of eggs available in the house.
 * The easter bunny is iterativaly stealing eggs (one at a time) according to 
 * the strategy 
 *     a[a[k]] := a[a[k]] - 1
 * until he visits a farm that ran out of eggs.
 * Is this a bad strategy because the easter bunny will eventually visit always
 * the same farm? Or is there some street and some choice of k in which the 
 * easter bunny can continue forever?
 * 
 * Date: 2014-04-05
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var k : int;

procedure main() returns ()
modifies a;
{
  while (a[a[k]] >= 0) {
    a[a[k]] := a[a[k]] - 1;
  }
}

