//#rNonTerminationDerivable
/*
 * Date: 2014-08-18
 * Author: Jan Leike
 *
 * Nonterminating
 *
 */
var a : [int] int;

procedure main(i : int) returns ()
modifies a;
{
  while (a[i] >= 0) {
    a[i] := a[i] + 1;
  }
}

