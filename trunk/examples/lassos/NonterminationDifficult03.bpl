//#rNonTerminationDerivable
/*
 * Date: 2015-09-01
 * Author: Jan Leike, Matthias Heizmann
 * Variant of NonTerminationTonChanh15.bpl where each variable has a 
 * coefficient. (We were surprised that we find a geometric nontermination
 * argument; however, this example is in fact simpler than 
 * NonTerminationTonChanh15.bpl because we have different eigenvalues and hence
 * it is diagonalizable).
 */

procedure main() returns (x: int, y: int)
{
  while (x >= 0) {
    x := 2 * x + 3 * y;
    y := 7 * y + 11;
  }
}

