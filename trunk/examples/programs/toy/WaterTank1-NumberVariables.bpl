//#Safe
/*
 * Date: 13.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * similar than the WaterTank.bpl but here we use variables to represent
 * big numbers
 *
 */

procedure waterTank()
{
  var time, fillLevel, increment, one, hundred, thousand: int;

  time := 0;
  fillLevel := 0;
  
  one := 1;
  hundred := 100 * one;
  thousand := 1000 * one;

  while ( time < hundred) {
    time := time +  1;
    fillLevel := fillLevel + 3;
  }

  assert( fillLevel <= thousand);
}
