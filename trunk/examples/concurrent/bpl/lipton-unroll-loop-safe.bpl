//#Safe
/*
 * Trace Abstraction unrolls the loop in thread 2. After each additional unrolling, repeated Lipton reduction is able
 * to fuse the unrolled loop body with a previous transition. Since the loop body contains an if/then/else, this
 * requires sequential compositions of actions with shared branch encoders.
 */
var a : [int]int;
var x : int;

procedure ULTIMATE.start()
modifies a, x;
{
  x := 0;

  fork 1   thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  assert x == 4 && a[0] >= 0 && a[1] >= 0 && a[2] >= 0 && a[3] >= 0 && a[4] >= 0;
}

procedure thread1()
modifies x;
{
  x := x + 1;
  x := x + 1;
  x := x + 1;
  x := x + 1;
}

procedure thread2()
modifies a;
{
  var i : int;
  i := 0;
  while (i < 5) {
    if (i < 4) {
      a[i] := 0;
    } else {
      a[i] := 1;
    }
    i := i + 1;
  }
}
