//#Safe
/*
 * Date: 2018-03-04
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var cakeLeft, eat, init: int;
  var m: [int]int;
  
  assume init >= 0;
  
  m[cakeLeft] := init;
  m[eat] := init / 2;
  
  while (*) 
      invariant cakeLeft == eat || (m[eat] + init / 2 <= m[cakeLeft] && m[eat] >= 0);
  {
    m[eat] := m[eat] / 2;
    m[cakeLeft] := m[cakeLeft] - m[eat];
  }
  if (cakeLeft != eat) {
    assert (m[cakeLeft] >= init / 2);
  }

} 
