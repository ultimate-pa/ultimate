//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-20
 * 
 */



procedure TerminatorSmall() returns () 
{
  var x, xAlt, y, yAlt, pcAlt: int;
  
  x := 23;
  while(pcAlt == 0)
  {
      pcAlt := 1;
      yAlt := y;
      xAlt := x;
      x := x - 1;
      havoc y;
  }
  assert pcAlt != 0;
  assert x == 23;
}
