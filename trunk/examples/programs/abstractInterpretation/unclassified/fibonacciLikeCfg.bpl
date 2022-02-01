//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 6.5.2011
 *
 * Program that returns a number >=0 and has a control structure similar to
 * fibonacci.bpl.
 */

procedure fibonacci(n: int) returns (res: int);

implementation fibonacci(n: int) returns (res: int)
{
  var tmpA, tmpB: int;

  if (*) {
    res := 0;
  }
  else {
    if (*) {
      res := 1;
    }
    else {
      call tmpA := fibonacci(n);
      call tmpB := fibonacci(n);
      res := tmpA + tmpB;
    }
  }
  assert(res >= 0);
}

