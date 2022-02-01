//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 3.8.2013
 *
 * Program that returns a number >=0 and has a control structure that has some
 * similarities with fibonacci.bpl.
 */

procedure main(n: int) returns (res: int);

implementation main(n: int) returns (res: int)
{
  var tmpA, tmpB: int;

    if (*) {
      res := 1;
    }
    else {
      call tmpA := main(n);
      call tmpB := main(n);
      res := tmpA + tmpB;
    }
  assert(res >= 0);
}

