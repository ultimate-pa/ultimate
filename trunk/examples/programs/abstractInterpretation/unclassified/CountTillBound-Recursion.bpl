//#Safe
/*
 * Variant of CountTillBound where a while loop is replaced by recursion.
 * Date: 23.09.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x: int;

procedure main()
modifies x;
{
  assume x == 0;
  call inc();
  assert(x == 100);
}

procedure inc()
modifies x;
{
  if(x < 100) {
    x := x + 1;
    call inc();
  }
}