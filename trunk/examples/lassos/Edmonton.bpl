//#rNonTerminationDerivable
/*
 * Date: 2015-09-07
 * Author: Jan Leike
 *
 * Conjunctive linear loop program that does not terminate
 * There is no (eigen)basis Y such that GY <= 0 (where G is the guard).
 * Nevertheless, there is a geometric nontermination argument.
 */

procedure main() returns (a, b: real)
{
  while (a >= 1.0 && b + 1.0 <= 0.0 && 0.0 <= a + b && a + b <= 5.0) {
    a := a * 2.0;
    b := b * 2.0;
  }
}
