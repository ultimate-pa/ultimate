//#Safe
/*
 * Variant of McCarthy's 91 function over the reals. The program is correct with
 * respect to assertions.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 6.3.2012
 *
 */

procedure McCarthy(x: real) returns (res: real);

implementation McCarthy(x: real) returns (res: real)
{

  if (x>100.0) {
    res := x-10.0;
  }
  else {
    call res := McCarthy(x + 11.0);
    call res := McCarthy(res);
  }
  assert(x > 101.0 || (90.0 <= res && res <= 91.0));
}

