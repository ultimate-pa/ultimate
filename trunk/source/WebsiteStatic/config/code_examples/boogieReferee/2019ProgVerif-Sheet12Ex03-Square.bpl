/* 
 * Program from Exercise 3 of sheet 12 in the lecture on program verification.
 * https://swt.informatik.uni-freiburg.de/teaching/SS2019/program-verification
 * Task: find a loop invariant that is sufficient to prove that the program
 * satisfies the given precondition-postcondition pair.
 * 
 * Author: Matthias Heizmann
 * Date: 2019-06-05
 */

procedure square(n: int) returns (res: int)
requires n > 2;
ensures res >= 2*n;
{
  var i, odd : int;
  i := 0;
  odd := 1;
  res := 0;
  while (i < n) {
    res := res + odd;
    odd := odd + 2;
    i := i + 1;
  }
}
