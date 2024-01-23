//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform well on.
 * DSR should only protect the variable x.
 *
 * Author: Veronika Klasen
 * Date: 2024-01-23
 */

  var x, y : int;

procedure ULTIMATE.start()
modifies x,y;
{

  fork 1   thread1();
  fork 2,2 thread2();
  join 1;
  join 2;
 
  assert x == 0;
}

procedure thread1()
modifies x, y;
{
	x := 0;
	y := x;
}

procedure thread2()
modifies y;
{
	y := 1;
}
