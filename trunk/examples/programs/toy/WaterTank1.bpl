//#Safe
/*
 * Date: 13.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Water tank is filled for 100 seconds
 * in every second to fill level increases by 3
 * 
 * We want to proof that the fill level is afterwards not higher
 * than 1000.
 *
 */

procedure waterTank()
{
  var time, fillLevel: int;

  time := 0;
  fillLevel := 0;
  
  while ( time < 100) {
    time := time +  1;
    fillLevel := fillLevel + 3;
  }

  assert( fillLevel <= 1000);
}