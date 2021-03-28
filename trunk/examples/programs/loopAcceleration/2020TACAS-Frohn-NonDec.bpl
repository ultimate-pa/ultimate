//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-03-27
 * 
 * Program non-dec from page 4 of the following publication.
 * 2020TACAS - Frohn - A Calculus for Modular Loop Acceleration.pdf
 */

procedure main() returns () {
  var x1, x2 : int;
  while(x1 > 0 && x2 > 0)
  {
      x1 := x1 - 1;
      x2 := x2 + 1;
  }
}


// Result of our Loop Acceleration:
// (or 
// 	(and (= x1' (- x1  n)) (= x2' (+ x2 n)) (<= x1 n) (< 0 n) (< 0 x2) (< n (+ x1 1))) 
// 	(and (= x1' x1) (= x2' x2) (= n 0) (or (<= x1 0) (<= x2 0)))
// )

