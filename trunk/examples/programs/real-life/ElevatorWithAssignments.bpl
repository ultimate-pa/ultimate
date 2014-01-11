//#Safe
/*
 * Date: 24.9.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Product of four phase event automata modeled as BoogiePL program.
 * Taken from Jochen Hoenickes PhD thesis
 * Combination of Processes, Data, and Time, University of Oldenburg, July 2006
 * http://csd.informatik.uni-oldenburg.de/~skript/pub/Papers/csp-oz-dc.pdf
 * 
 */

procedure Elevator()
{
  // event variables
  var newgoal, start, stop, passed: bool;

  // constants
  var min, max: int;

  // data variables
  var current, goal, dir: int;

  // clocks
  var c2: int;
  var c3: int;

  // variables for increase of clocks
  var timeIncrease: int;

  // variables for locations  
  var qCSP: int;
  var qDC1: int;
  var qDC2: int;

  assume (min < max);
  goal := min;
  current := min;
  dir := 0;
  c2 := 0;
  c3 := 0;
  qCSP := 1;
  qDC1 := 1;
  qDC2 := 1;


  while (*) 
     invariant (min <= current && current <= max
/*      && (qCSP == 1 ==> current == goal && qDC2 == 1)
      && (qCSP == 2 ==> qDC2 == 2 && current != goal)
      && (qCSP == 3 && current < goal ==> qDC2 == 2 && dir == 1)
      && (qCSP == 3 && current > goal ==> qDC2 == 2 && dir == -1)
      && (qCSP == 3 && current == goal ==> qDC2 == 3 && qDC1 == 2 && c2 == c3)
*/
);
  {
    
    havoc newgoal;
    havoc start;
    havoc stop;
    havoc passed;

    havoc timeIncrease;
    assume (timeIncrease >= 0);
    c2 := c2 + timeIncrease;
    c3 := c3 + timeIncrease;
    if (qDC1 == 2) {
      assume c2 <= 3;
    }
    if (qDC2 == 3) {
      assume c3 <= 2;
    }

    
    
    // Automaton CSP, page 99
    if (qCSP == 1 && !newgoal && !start && !stop && !passed) {
    }
    else if (qCSP == 1 && newgoal && !start && !stop && !passed) {
        qCSP := 2;
    }
    else if (qCSP == 2 && !newgoal && !start && !stop && !passed) {
    }
    else if (qCSP == 2 && !newgoal && start && !stop && !passed) {
        qCSP := 3;
    }
    else if (qCSP == 3 && !newgoal && !start && !stop && !passed) {
    }
    else if (qCSP == 3 && !newgoal && !start && !stop && passed) {
    }
    else if (qCSP == 3 && !newgoal && !start && stop && !passed) {
        qCSP := 1;
    }
    else {
      assume false;
    }

    // Automaton Z, page 102
    if (!newgoal && !start && !stop && !passed) {
    }
    else if (newgoal && !start && !stop && !passed) {
      havoc goal;
      assume (min <= goal);
      assume (goal <= max);
      assume (goal != current);
    }
    else if (!newgoal && start && !stop && !passed) {
      havoc dir;
      assume (goal > current ==> dir==1);
      assume (goal < current ==> dir==-1);
    }
    else if (!newgoal && !start && stop && !passed) {
      assume (goal == current);
    }
    else if (!newgoal && !start && !stop && passed) {
      current := current + dir;
    }
    else {
      assume false;
    }
    
    // DC Automaton 1, page 139
    if (qDC1 == 1 && passed) {
      c2 := 0;
      qDC1 := 2;
    }
    else if (qDC1 == 1 && !passed) {
      
    }
    else if (qDC1 == 2 && !passed && c2 < 3) {
      
    }
    else if (qDC1 == 2 && !passed && c2 >= 3) {
      qDC1 := 1;
    }
    else {
      assume false;
    }
    
    // DC Automaton 2, page 139
    if (qDC2 == 1 && current==goal) {
    }
    else if (qDC2 == 1 && current!=goal) {
      qDC2 := 2;
    }
    else if (qDC2 == 2 && current!=goal) {
      
    }
    else if (qDC2 == 2 && current==goal) {
      qDC2 := 3;
      c3 := 0;
    }
    else if (qDC2 == 3 && !stop ) {
      assume (c3 < 2);
    }
    else if (qDC2 == 3 && stop) {
      qDC2 := 1;
    }
    else {
       assume false;
    }
  }

}

