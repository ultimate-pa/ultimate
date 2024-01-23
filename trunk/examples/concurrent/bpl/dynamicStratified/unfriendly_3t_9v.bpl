//#Safe

/**
 * A small example program that dynamic stratified reduction is expected to perform poorly on.
 * Contains a loop;
 *
 * Number of threads: 3
 * Number of variables: 10 (+ loop var)
 *
 * Author: Veronika Klasen
 * Date: 2024-01-23
 */

  var x, y1, y2, y3, y4, y5, y6, y7, y8, y9: int;
  var i : int;

procedure ULTIMATE.start()
modifies i, x ,y1, y2, y3, y4, y5, y6, y7, y8, y9;
{
  i := 0;
  while (i < 5) {
	i := i + 1;
  }
  fork 1   thread1();
  fork 2,2 thread2();
  fork 3,3,3 thread3();
  join 1;
  join 2,2;
  join 3,3,3;
 
  assert x == 0;
}

procedure thread1()
modifies x, y1, y2, y3, y4, y5, y6, y7, y8, y9;
{
	x := 0;
	y9 := x;
}

procedure thread2()
modifies y1, y2, y3, y4, y5, y6, y7, y8, y9;
{
	y1 := 1;
	y2 := 3 * x + y1;
	y3 := y1;
	y4 := y3 + x;
	y5 := 8 * y2;
	y6 := y2 + y3;
	y7 := 1 - y5;
	y8 := y1 + y3;
	y9 := y8 * y7 * x;
}

procedure thread3()
modifies y1, y2, y3, y4, y5, y6, y7, y8, y9;
{
	y1 := x;
	y2 := 3 * x + y1;
	y3 := y2 - y1;
	y4 := y1 * y2 * y3;
	y5 := y3 + y2;
	y6 := 7;
	y7 := y6 * 8;
	y8 := y3;
	y9 := y4 + y5 * x + y7;
	
}
