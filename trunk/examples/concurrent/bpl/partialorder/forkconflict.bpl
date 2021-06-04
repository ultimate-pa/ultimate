//#Unsafe

/**
 * Illustrates a fork conflict (persistent set reduction):
 * When Thread1 and Thread2 have both been forked, the persistent set must necessarily include the actions of Thread2:
 * Even though Thread1 does not have a commutativity conflict with Thread2, it has a conflict with Thread3, which is forked by Thread2.
 *
 * Without the introduction of *fork conflicts*, verification with persistent set reduction may incorrectly declare this program correct.
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2021-05-27
 */

var x, y : int;

procedure ULTIMATE.start()
modifies x, y;
{
  x := 0;
  y := 0;

  fork 1 Thread1();
  fork 2,2 Thread2();
  join 1;

  assert x == 0;
}

procedure Thread1()
modifies x;
{
  x := y;
}

procedure Thread2()
modifies y;
{
  fork 3,3,3 Thread3();
}

procedure Thread3()
modifies y;
{
  y := 1;
}
