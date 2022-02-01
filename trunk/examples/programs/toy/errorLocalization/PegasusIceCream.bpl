//#Unsafe
/* Example shows that our the definition for relevancy of an assignment
 * that we had before May 2017 deviates from the result of the algorithm.
 * 
 * Problem the assignment "y := 42" is irrelevant (according to algorithm),
 * but is was relevant according to the definition because the 
 * statement "assume(x >= 0)" is restrictive.
 * 
 * 
 * Author: Matthias Heizmann
 * Date: 2017-05-29
 * 
 * 
 */

procedure main() returns () {
  var x, y : int;
  y := 42;
  havoc x;
  assume(x >= 0);
  assert(false);
}


