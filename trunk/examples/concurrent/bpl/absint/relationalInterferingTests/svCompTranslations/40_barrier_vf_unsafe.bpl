//#Unsafe

var count: int;
var COND: bool;

procedure thread1()
modifies count, COND;
{
  atomic {
    count := count + 1;
    if (count == 3) {
      COND := true;
      count := 0;
    }
  }

  while (!COND) {
    assume true;
  }

  assert false;
}

procedure ULTIMATE.start()
modifies count, COND;
{
  count := 0;
  COND := false;

  while (true) {
    fork 1 thread1();
  }
}

