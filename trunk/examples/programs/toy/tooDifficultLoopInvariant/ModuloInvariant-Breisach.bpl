//#Safe
/*
 * Most simple example that I can imagine where we need an invariant with modulo.
 * 
 * Date: 2016-12-27
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  assume x % 7 == 0;

  while (*) {
    x := x + 7;
  }

  assert (x % 7 == 0);

} 
