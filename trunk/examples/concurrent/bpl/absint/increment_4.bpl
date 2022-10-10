//#Safe

/*
 *
 */

var x0: int;
var x1: int;
var x2: int;
var x3: int;

procedure thread1() returns()
modifies x1;
{
  x1 := x0 + 1;
}

procedure thread2() returns()
modifies x2;
{
  x2 := x1 + 1;
}

procedure thread3() returns()
modifies x3;
{
  x3 := x2 + 1;
}

procedure ULTIMATE.start() returns()
modifies x0, x1, x2, x3;
{
  
  x0 := 0;
  x1 := 0;
  x2 := 0;
  x3 := 0;

  while (*) {
    fork 1 thread1();
    fork 2 thread2();
    fork 3 thread3();
  }

  assert x0 == 0 && x1 >= 0 && x2 >= 0 && x3 >= 0;
}
