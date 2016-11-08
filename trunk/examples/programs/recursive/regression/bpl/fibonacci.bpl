//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 6.5.2011
 *
 * Recursive computation of fibonacci numbers.
 */

procedure fibonacci(n: int) returns (res: int);
ensures res >= 0;

implementation fibonacci(n: int) returns (res: int)
{
  var tmpFst, tmpSnd: int;

  if (n < 1) {
    res := 0;
  }
  else {
    if (n == 1) {
      res := 1;
    }
    else {
      call tmpFst := fibonacci(n-1);
      call tmpSnd := fibonacci(n-2);
      res := tmpFst + tmpSnd;
    }
  }
}

