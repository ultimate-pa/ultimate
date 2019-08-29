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
  var current', goal', dir': int;

  // clocks
  var c2: real;
  var c3: real;

  // variables for increase of clocks
  var timeIncrease: real;

  // variables for locations
  var qCSP: int;
  var qDC1: int;
  var qDC2: int;

  assume (min < max);
  assume (min <= current);
  assume (current <= max);
  goal := current;
  c2 := 0.0;
  c3 := 0.0;
  qCSP := 1;
  qDC1 := 1;
  qDC2 := 1;


  while (*)
/*
    invariant (
//(((((((min <= goal' || 0 <= qCSP + -3) || qCSP <= 1) && ((((((((c2 <= c3 && 0 <= c3) && !(qCSP + -1 == 0)) && qDC2 + -3 == 0) && (current' <= goal' || -1 == dir')) && qDC1 + -2 == 0) || ((!(qCSP + -1 == 0) && goal' <= current' + -1) && !(qCSP + -3 == 0))) || qDC2 + -1 <= 0) || (((qDC2 + -2 == 0 && (current' <= goal' + -1 || goal' <= current' + -1)) && !(qCSP + -1 == 0)) && min <= goal'))) && ((((qDC2 + -2 == 0 && (goal' + 1 <= current' || 1 == dir')) || ((!(qCSP + -1 == 0) || 0 <= qDC2 + -1) && (((current' <= goal' && goal' <= current') && !(qCSP + -3 == 0)) || (((qCSP <= 2 || 0 <= qCSP + -4) && 0 <= qDC2 + -2) && qDC2 <= 2)))) || ((((!(qCSP + -1 <= 0) && c2 <= c3) && 0 <= c3) && qDC2 + -3 == 0) && qDC1 + -2 == 0)) || ((((((current' <= goal' && !(qCSP + -1 == 0)) && qDC2 <= 1) && 0 <= qDC2 + -1) && dir' <= 0) && 0 <= dir') && !(qCSP + -3 == 0)))) && current' <= max) && goal' <= max) && (((((!(qCSP + -2 == 0) && (current' <= goal' || (0 <= dir' && dir' <= 0))) || (!(qCSP + -2 == 0) && !(qCSP + -3 == 0))) || ((qDC2 + -2 <= 0 && -1 == dir') && !(qDC2 + -1 <= 0))) || ((qCSP <= 2 && qDC2 + -2 <= 0) && !(qDC2 + -1 <= 0))) || ((qDC2 + -3 == 0 && min <= goal') && !(qCSP + -2 == 0)))) && min <= current'
	      (qCSP == 2 ==> current != goal) &&
	      (qCSP == 3 && current < goal ==> dir == 1) &&
	      (qCSP == 3 && current > goal ==> dir == -1) &&
	      (qCSP == 3 && current == goal ==> qDC2 != 1 && qDC1 == 2 && c2 <= c3) &&
	      min <= goal && goal <= max &&
	min <= current && current <= max
    );*/
  {

    havoc timeIncrease;
    assume (timeIncrease > 0.0);
    c2 := c2 + timeIncrease;
    c3 := c3 + timeIncrease;

    if (qDC1 == 2) {
      assume (c2 <= 3.0);
    }

    if (qDC2 == 1) {
      assume (current == goal);
    } else if (qDC2 == 2) {
      assume (current != goal);
    } else if (qDC2 == 3) {
      assume (current == goal);
      assume (c3 < 2.0);
    }

    assert (min <= current && current <= max);

    havoc newgoal;
    havoc start;
    havoc stop;
    havoc passed;

    havoc current';
    havoc goal';
    havoc dir';

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
      assume (current'==current);
      assume (goal'==goal);
      assume (dir'==dir);
    }
    else if (newgoal && !start && !stop && !passed) {
      assume (min <= goal');
      assume (goal' <= max);
      assume (goal' != current);
      assume (current'==current);
      assume (dir'==dir);
    }
    else if (!newgoal && start && !stop && !passed) {
      assume (goal > current ==> dir'==1);
      assume (goal < current ==> dir'==-1);
      assume (current'==current);
      assume (goal'==goal);
    }
    else if (!newgoal && !start && stop && !passed) {
      assume (goal == current);
      assume (current'==current);
      assume (goal'==goal);
      assume (dir'==dir);
    }
    else if (!newgoal && !start && !stop && passed) {
      assume (current' == current + dir);
      assume (goal'==goal);
      assume (dir'==dir);
    }
    else {
      assume false;
    }

    // DC Automaton 1, page 139
    if (qDC1 == 1) {
      if (*) {
         assume !passed;
      } else {
         assume passed;
	 c2 := 0.0;
         qDC1 := 2;
      }
    } else if (qDC1 == 2) {
      if (*) {
         assume !passed;
      } else {
         assume !passed && c2 >= 3.0;
	 qDC1 := 1;
      }
    } else {
      assume false;
    }

    // DC Automaton 2, page 139
    if (qDC2 == 1) {
        if (*) {
	   // stuttering edge
    	} else {
	   qDC2 := 2;
        }
    } else if (qDC2 == 2) {
        if (*) {
	    // stuttering edge
	} else {
            qDC2 := 3;
            c3 := 0.0;
        }
    } else if (qDC2 == 3) {
        if (*) {
	    assume !stop;
	    // stuttering edge
	} else {
	    assume stop;
	    qDC2 := 1;
	}
    } else {
       assume false;
    }

    current := current';
    goal := goal';
    dir := dir';
  }

}

