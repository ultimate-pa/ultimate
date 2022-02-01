//#Unsafe
/*
 * Date: 12.09.2011
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Version of GateController with inserted Bug.
 */

procedure GateController()
{
  var gate, time, time_increment: int;
  var alarm: bool;
  var one, maxGatePosition, thousand: int;
  
  one := 1;
  maxGatePosition := 100 * one;
  thousand := 1000 * one;


  gate := 0;
  time := 0;
  alarm := false;
  
  while ( time < thousand) {
    if (gate < maxGatePosition) {
      gate := gate + 1;
    }
    havoc time_increment;
    if ( time_increment > 99) {
      alarm := true;
    }
    time := time + time_increment;
  }

  assert( alarm || gate == maxGatePosition);
}
