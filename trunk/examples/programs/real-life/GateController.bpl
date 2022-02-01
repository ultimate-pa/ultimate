//#Safe
/*
 * Date: 24.08.2011
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Model of a GateController.
 * The Controller iteratively modifies the gate position (gate:= gate +1) for a
 * thousand milliseconds. If an iteration takes more than 10 milliseconds the
 * an alarm is raised.
 * Our correctness specification: After all iterations either the gate has 
 * reached maxGatePosition or an alarm was raised.
 *
 * Inspired by water tank examples.
 * Challange: Tool has to infer the invariant gate*10>=time
 *
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
    if ( time_increment > 10) {
      alarm := true;
    }
    time := time + time_increment;
  }

  assert( alarm || gate == maxGatePosition);
}
