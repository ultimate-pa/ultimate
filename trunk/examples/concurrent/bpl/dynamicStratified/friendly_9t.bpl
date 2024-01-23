//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform well on.
 * DSR should only protect the variable x.
 *
 * Number of threads: 9
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
  fork 4,4,4,4 thread4();
  fork 5,5,5,5,5 thread5();
  fork 6,6,6,6,6,6 thread6();
  fork 7,7,7,7,7,7,7 thread7();
  fork 8,8,8,8,8,8,8,8 thread8();
  fork 9,9,9,9,9,9,9,9,9 thread9();
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;
  join 5,5,5,5,5;
  join 6,6,6,6,6,6;
  join 7,7,7,7,7,7,7;
  join 8,8,8,8,8,8,8,8;
  join 9,9,9,9,9,9,9,9,9;
 
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
procedure thread6()
modifies y;
{
	y := 6;
}

procedure thread7()
modifies y;
{
	y := 7;
}

procedure thread8()
modifies y;
{
	y := 8;
}

procedure thread9()
modifies y;
{
	y := 9;
}



