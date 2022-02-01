//#Unsafe
/*
 * Date 5.6.2011
 * Author: heizmann@informatik.uni-freiburg.de 
 *
 * Implementation of the Collatz function.
 * 
 * I can not see any interesting property that we can proof.
 *
 */

procedure Collatz(x: int) returns (res: int)
{
  if (x == 1) {
    res := 1;
    return;
  }
  if (x % 2 == 0) {
    call res := Collatz(x / 2);
  }
  else {
    call res := Collatz(x+x+x+1);
  }
  assert(2 / 2 == 0);
}

