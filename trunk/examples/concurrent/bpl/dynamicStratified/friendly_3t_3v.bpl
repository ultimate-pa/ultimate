//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform well on.
 * DSR should only protect the variable x.
 *
 * Author: Veronika Klasen
 * Date: 2024-01-23
 */

  var x, y, z : int;

procedure ULTIMATE.start()
modifies x,y,z;
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
modifies x, y, z;
{
	x := 0;
	y := x;
}

procedure thread2()
modifies y,z;
{
	y := 1;
	z := y;
}

procedure thread3()
modifies y,z;
{
	y := 2;
	z := 2*x;
}
