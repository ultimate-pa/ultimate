//#Safe
/*
 * Integer version of the geometrical cake example.
 * 
 * Prefix of execution
 * (cakeLeft, eat)
 * (2000, 1000)
 * (1500, 500)
 * (1250, 250)
 * (1125, 125)
 * 
 * The following loop invariant is sufficient to prove correctness.
 * eat >=0 && eat + 1000 <= cakeLeft
 * 
 * Date: 2017-08-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var cakeLeft, eat, init: int;
  
  assume init >= 0;
  
  cakeLeft := init;
  eat := init / 2;
  
  while (*) 
      invariant cakeLeft + eat >= init / 2 && eat >=0;
  {
    eat := eat / 2;
    cakeLeft := cakeLeft - eat;
  }

  assert (cakeLeft >= init / 2);

} 
