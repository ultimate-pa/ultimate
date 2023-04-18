//#rTerminationDerivable
/*
 * Date: 2014-10-03
 *
 * Author: Jan Leike
 *
 * The loop transition is unsatisfiable,
 * hence any function is a ranking function.
 */

procedure main() returns (x: int)
{
  assume true;
  while (true) {
    x := 0;
    assume(x > 0);
  }
}

