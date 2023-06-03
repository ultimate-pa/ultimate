/* 
 * Program from Exercise 4 of sheet 12 in the lecture on program verification.
 * https://swt.informatik.uni-freiburg.de/teaching/SS2019/program-verification
 * Task: find a loop invariant that is sufficient to prove that the program
 * satisfies the given precondition-postcondition pair.
 * 
 * Author: Tanja Schindler, Dominik Klumpp
 * Date: 2019-06-05
 */

procedure findmin(a : [int, int]int, lo : int, hi : int) returns (min : int)
  requires lo <= hi;
  ensures (forall i, j : int :: lo <= i && i <= hi && lo <= j && j <= hi
    ==> a[i, j] >= min);
{
  var i, j : int;

  i := lo;
  min := a[lo, lo];

  while (i <= hi) {
    j := lo;
    while (j <= hi) {
      if (a[i, j] < min) {
        min := a[i, j];
      }

      j := j + 1;
    }

    i := i + 1;
  }
}
