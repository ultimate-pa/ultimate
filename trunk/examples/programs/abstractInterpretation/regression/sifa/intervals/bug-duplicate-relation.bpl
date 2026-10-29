//#Safe
/* 
 * In previous versions IntervalDomain.CompareNumberOfFreeVariablesInRhs
 * crashed, since x <= 0.0 and 2.0 * x <= 0.0 produce the same
 * SolvedBinaryRelation.
 * 
 * Author: schuessf@informatik.uni-freiburg.de
 * Date: 2026-10-12
 */
procedure main() {
  var x : real;
  var y : int;
  
  assume x <= 0.0 && 2.0 * x <= 0.0;
  y := 0;
  
  // Loop to reveal bug when using not always fluid
  while (*) {
    y := y + 1;
  }
  
  assert x <= 0.0;
}
