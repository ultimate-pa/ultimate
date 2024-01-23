//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform horribly on.
 * Contains a loop.
 *
 * Author: Veronika Klasen
 * Date: 2024-01-23
 */

  var x, y, z, i : int;

procedure ULTIMATE.start()
modifies i, x,y,z;
{	
  i := 0;
  x := i;
  fork 1   thread1();
  fork 2,2 thread2();
  fork 3,3,3 thread3();
  join 1;
  join 2,2;
  join 3,3,3;
  while (i < 5) {
	i := i + 1;
  }
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
