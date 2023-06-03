//#rNonTerminationDerivable
/*
 * Date: 2015-06-29
 * Author: leike@informatik.uni-freiburg.de
 *
 * Nonterminating loop that can be partitioned into two
 * nonterminating loops with the LassoPartitioneer.
 * It is a test case for the correct reassembly of nontermination arguments.
 */

procedure NonTerminationSimple() returns (x: int, y: int)
{
  while (true) {
    x := x + 1;
    y := y + 2;
  }
}

