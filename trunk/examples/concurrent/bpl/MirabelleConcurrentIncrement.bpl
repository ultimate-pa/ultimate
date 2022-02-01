//#Safe
/*
 * 
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2019-08-12
 * 
 */

var x, y, n : int;

procedure ULTIMATE.start()
  modifies x,y;
{

  assume x == y;

  fork 1 T1();
  fork 2 T2();

  join 1;
  join 2;

  assert x == y;

}

procedure T1()
  modifies x;
{
  while (x < n) {
    x := x + 1;
  }
}

procedure T2()
  modifies y;
{
  while (y < n) {
    y := y + 1;
  }
}
