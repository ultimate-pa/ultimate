//#rNonTerminationDerivable
/*
 * In revision 11466 there is probly a bug, because I get the following result
 * which hints that a and b were reassigned before the loop.
 *  NonTermination argument in form of an infinite program execution.
 *  NonTermination argument in form of an infinite execution
 *  {proc_a=0, proc_b=0}
 *  {proc_a=7, proc_b=8}
 *  {proc_a=8, proc_b=9}
 *  {proc_a=9, proc_b=10}
 *
 * Date: 29.04.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure proc() returns ()
{
  var a,b:int;
  assume(true);
  while (a >= 7) {
    a := b;
    b := a + 1;
  }
}

