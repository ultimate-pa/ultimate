//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform well on.
 * DSR should only protect the variable x.
 * Number of threads : 9
 * Number of variables: 2
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
  fork 3,3,3 thread3();
  join 1;
  join 2,2;
  join 3,3,3;
 
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

procedure thread3()
modifies y;
{
	y := 2;
}
