//#Safe
/*
 * 
 * Date: 2017-08-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var cakeLeft, eat: real;
  
  cakeLeft := 1.0;
  eat := 0.5;
  
  while (*) {
    eat := eat / 2.0001;
    cakeLeft := cakeLeft - eat;
  }

  assert (cakeLeft >= 0.0);

} 
