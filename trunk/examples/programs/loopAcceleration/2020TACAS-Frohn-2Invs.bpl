//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2020-12-29
 * 
 * Program 2-invs from page 5 of the following publication.
 * 2020TACAS - Frohn - A Calculus for Modular Loop Acceleration.pdf
 */

procedure main() returns () {
  var x1, x2 : int;
  while(x1 > 0 && x2 > 0)
  {
      x1 := x1 + x2;
      x2 := x2 - 1;
  }
}


