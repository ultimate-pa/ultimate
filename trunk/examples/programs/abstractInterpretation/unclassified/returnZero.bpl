//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 8.5.2011
 * 
 * Small example to reproduce the wrong invariant bug.
 * Reason for wrong invariant was bug in difference.
 *
 */


procedure returnZero(n: int) returns (res: int);

implementation returnZero(n: int) returns (res: int)
{
  var tmp: int;

  if (*) {
    res := 0;
  }
  else {
    call tmp := returnZero(n);
    call tmp := returnZero(n);
    call tmp := returnZero(n);
    call tmp := returnZero(n);
    res := tmp;
  }
  assert(res >= 0);
}

