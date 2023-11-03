//#Safe
/*
 * A program that demonstrates how important Large Block Encoding can be.
 * This is the program shown in my Bachelor's thesis.
 *
 * Author: Elisabeth Schanno (elisabeth.schanno@venus.uni-freiburg.de)
 * Date: 2019-10-21
 * 
 */

var x : bool;

procedure ULTIMATE.start();
modifies x;

implementation ULTIMATE.start()
{
  x := true;
  fork 1 bar();
  fork 2 bar();
  fork 3 bar();
  fork 4 bar();
  assert x;
  assert x;
  join 4;
  join 3;
  join 2;
  join 1;
}

procedure bar();

implementation bar()
{
  assert x;
  assert x;
  assert x;
  assert x;
  assert x;
  assert x;
  assert x;
  assert x;
  assert x;
}