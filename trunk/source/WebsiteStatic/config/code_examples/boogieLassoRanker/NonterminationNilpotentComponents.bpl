//#rNonTerminationDerivable
/*
 * Date: 2016-01-12
 * Author: Jan Leike
 *
 * Needs a GTNA with nilpotent components
 * even though the loop transition matrix M is diagonalizable
 * 
 * (Variant of NonterminationDifficult08.bpl)
 * 
 * a grows exponential, hence faster than b
 * 
 */

procedure main() returns (a, b: real)
{
  while (a - b >= 0.0 && b >= 0.0) {
    a := 3.0*a;
    b := b + 1.0;
  }
}

