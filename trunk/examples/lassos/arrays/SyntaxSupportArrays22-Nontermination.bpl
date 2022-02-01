//#rNonTerminationDerivable
/*
 * Date: 2014-08-18
 * Author: Jan Leike
 *
 * Nonterminating
 *
 */
var a : [int] int;

procedure main() returns ()
modifies a;
{
  assume true;
  while (a[0] >= 0) {
    a[0] := a[0] + 1;
  }
}

