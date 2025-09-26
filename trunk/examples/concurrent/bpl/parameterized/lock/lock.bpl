//#Safe

var lock : bool;
var ctr : int;
var x : int;

procedure ULTIMATE.start()
free requires ctr == 0;
modifies ctr, lock, x;
{
  atomic {
    assume !lock;
    lock := true;
    ctr := ctr + 1;
  }

  // critical section
  x := x + 1;
  x := x + 1;
  x := x + 1;
  x := x + 1;

  // no one else is in the critical section
  assert ctr < 2;

  atomic {
    lock := false;
    ctr := ctr - 1;
  }
}
