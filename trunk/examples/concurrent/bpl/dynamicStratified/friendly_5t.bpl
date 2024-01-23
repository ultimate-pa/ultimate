//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform well on.
 *
 * Number of threads: 5
 * Number of variables: 2
 *
 * Author: Veronika Klasen
 * Date: 2024-01-23
 */

  var x, y : int;

procedure ULTIMATE.start()
modifies x, y;
{

  fork 1   thread1();
  fork 2,2 thread2();
  fork 3,3,3 thread3();
  fork 4,4,4,4 thread4();
  fork 5,5,5,5,5 thread5();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;
  join 5,5,5,5,5;
 
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
	y := 2;
}

procedure thread3()
modifies y;
{
	y := 3;
}

procedure thread4()
modifies y;
{
	y := 4;
}

procedure thread5()
modifies y;
{
	y := 5;
}