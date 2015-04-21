//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Simple Program which is correct with respect to assertions.
 * In order to proof correctness one has to infer loop invariants e.g. x>=0
 *
 * The example is taken from our SAS'09 paper "Refinement of Trace Abstraction".
 * http://www.springerlink.com/content/d372357375t64146/fulltext.pdf
 *
 */

procedure main()
{
  var x, y: int;

  assume y >= 5;
  while (*) {
  }
  assert(y > 4);
}

