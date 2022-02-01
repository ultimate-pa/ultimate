//#Safe
/*
 * Date: 24.08.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Example inspired by water tank examples.
 *
 */

procedure GateController()
{
  var one, hundred, thousand: int;
  var gate, time, increment: int;
  var gateMotorFailure, alarmTrain: bool;

  gate := 0;
  time := 0;
  
  one := 1;
  hundred := 100 * one;
  thousand := 1000 * one;
  alarmTrain := false;
  

  while ( time < thousand) {
    if (*) { gateMotorFailure := true; }
    if (gateMotorFailure) {
      alarmTrain := true;
    } else {
      if (gate < hundred) {
	gate := gate + 1;
      }
    }
    havoc increment;
    assume (increment < 10);
    time := time + increment;
  }

  assert( alarmTrain || gate == hundred);
}
