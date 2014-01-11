//#Safe
/*
 * Date: 14.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * opposed to WaterTank.bpl the fillLevel is not incremented by exactly
 * three, but by some number less than or equal to three
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
    havoc increment;
    assume (increment <= 3);
    fillLevel := fillLevel + increment;
  }

  assert( fillLevel <= thousand);
}
