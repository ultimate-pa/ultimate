//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 16.05.2011
 *
 * Reveales Bug in revision r3700.
 * Construction of RCFG fails. Procedures final node is not constructed because
 * it is not reachable. At the end an imaginary auxiliary return statement is
 * processed. This fails because final node is missing.
 * Fixed in later revisions.
 */

procedure loop()
{
  var x : int;
  x := 0;
  
  loop:

  x := x + 1;
  assert(x != -1);

  goto loop;
}



