//#Safe
/*
 * Bug in sequential composition in r6186
 * 
 * Date: 06.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 *
 */

procedure GateController()
{
  var gate, time, time_increment: int;
  var alarm: bool;
  var one, y, thousand: int;
  
  one := 1;
  y := one;
  assert (one == 1);
}
