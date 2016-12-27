//#Safe
/*
 * Most simple example that I can imagine where we need a modulo operation in 
 * the invariant synthesis.
 * 
 * Date: 2016-12-27
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  x := 8;

  while (*) {
    // break LBE
  }
  
  x := x % 7;
  
  while (*) {
    // break LBE
  }

  assert (x <= 1);

} 
