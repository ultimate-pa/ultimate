//#Safe
/*
 * Author: ???
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

/*
 Author: musab@informatik.uni-freiburg.de
 This program is an example from by bachelor thesis.
 Program is correct with respect to the specification.
 ULTIMATE can prove its correctness.
 It needs 11 iterations, and it takes ~10 seconds to prove it, if we compute
 the state assertions with SP / WP.
 ULTIMATE needs only 6 iterations, and it takes ~1.5 seconds to prove it,
 if we compute the state assertions only for those statements, which appear
 in the unsatisfiable core of the corresponding infeasibility proof.
 For the other statements we compute some "simple" state assertions.
*/

procedure Main(z : int) returns ();
requires z >= 0;

implementation Main(z : int) returns () {
  var x, y : int;
  x := 0;
  y := x;
  while(x < z) {
    x := x + 1;
  }
  assert(y == 0);
  assert(x >= 0);
}


