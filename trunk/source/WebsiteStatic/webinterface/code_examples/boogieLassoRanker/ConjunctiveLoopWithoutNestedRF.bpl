//#rTermination
/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 * This is a terminating conjunctive linear loop program that is suspected
 * to have no nested or multiphase ranking function.
 *
 * The variables a and b are positive and grow exponentially, but b grows
 * faster than a. For any input, b eventually becomes larger than a and from
 * then on q decreases until it becomes negative.
 * Therefore the program terminates.
 *
 * Ultimate (revision 11762) says there is no k-nested or k-phase ranking
 * function for k <= 30.
 */

procedure main() returns ()
{
  var q, a, b: real;
  while (q >= 0.0 && a >= 1.0 && b >= 1.0) {
    q    := q + a - b;
    a    := 2.0*a;
    b    := 3.0*b;
  }
}
