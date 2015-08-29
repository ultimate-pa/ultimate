//#rNonTerminationDerivable
/* The values of x and y are increasing at different speeds.
 * However, y can use a positive value to compensate its slower speed.
 * The value of z is obtained nondeterministically and delayed by one iteration.
 * Hence, the 'havoc w' has to guess which value is needed by z in the next
 * iteration.
 * 
 * This is one example of the "convincing nondeterminism" series.
 * Examples of this series should demonstrate in a convincing way that 
 * nondeterministic conjunctive lasso programs are more powerful than 
 * deterministic conjunctive lasso programs.
 * 
 * Date: 2015-07-29
 * Author: Matthias Heizmann
 */

procedure main() returns ()
{
  var x,y,z,w: int;
  while (x == y && z > 0) {
    havoc w;
    x := 2 * x;
    y := y + 1 + z;
    z := w;
  }
}

