//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Implementation of McCarthy's 91 function. The program is correct with
 * respect to assertions.
 * In order to proof correctness one has to infer some requires/ensures pairs
 *
 * The example is taken from our POPL'10 paper "Nested Interpolants".
 */

procedure McCarthy(x: int) returns (res: int);

implementation McCarthy(x: int) returns (res: int)
{
  if (x > 100) {
    res := x - 10;
  }
  else {
    call res := McCarthy(x + 11);
    call res := McCarthy(res);
  }
  assert(res == 91 || x > 101);
}

