//#Safe

/*
 * Extracted from: svcomp/pthread-ext/31_simple_loop5_vs.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-02-09
 *
 */

var a, b, c, temp, m: int;

procedure thread1() returns()
modifies m;
{
  while (true) {
    atomic { assume m == 0; m := 1; }
    assert a != b;
    atomic { assume m == 1; m := 0; }
  }
}

procedure thread2() returns()
modifies a, b, c, temp, m;
{
  while (true) {
    atomic { assume m == 0; m := 1; }
    temp := a;
    a := b;
    b := c;
    c := temp;
    atomic { assume m == 1; m := 0; }
  }
}

procedure ULTIMATE.start() returns()
modifies a, b, c, temp, m;
{
  a := 1;
  b := 2;
  c := 3;
  
  fork 0 thread1();
  while (true) {
    fork 0 thread2();
  }
}