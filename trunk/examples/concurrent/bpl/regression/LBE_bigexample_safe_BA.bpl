//#Safe
/*
 * A program that demonstrates how important Large Block Encoding can be.
 * This is the program shown in my Bachelor's thesis.
 *
 * Author: Elisabeth Schanno (elisabeth.schanno@venus.uni-freiburg.de)
 * Date: 2019-10-21
 * 
 */

var x : int;

procedure ULTIMATE.start();
modifies x;

implementation ULTIMATE.start()
{
  x := 1;
  fork 1 bar();
  fork 2 bar();
  fork 3 bar();
  fork 4 bar();
  assert x != 0;
  assert x != 0;
  join 4;
  join 3;
  join 2;
  join 1;
}

procedure bar();

implementation bar()
{
  assert x != 0;
  assert x != 0;
  assert x != 0;
  assert x != 0;
  assert x != 0;
  assert x != 0;
  assert x != 0;
  assert x != 0;
  assert x != 0;
}