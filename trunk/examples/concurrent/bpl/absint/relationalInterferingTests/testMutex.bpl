//#Safe
/*
*/

var mutex : bool;
var crit : int;

procedure ULTIMATE.start()
modifies mutex, crit;
{
    mutex := false;
    crit := 0;
    fork 1 Thread1();
    fork 2 Thread2();
}

procedure Thread1()
modifies mutex, crit;
{
    atomic {
      call acquire_lock();
    }
    assert crit == 0;
    crit := 1;
    assert crit == 1;
    crit := 0;
    mutex := false;
}

procedure Thread2()
modifies mutex, crit;
{
    atomic {
      call acquire_lock();
    }
    assert crit == 0;
    crit := 2;
    assert crit == 2;
    crit := 0;
    mutex := false;
}

procedure acquire_lock()
modifies mutex;
{
  if (mutex) {
      assume false;
  }
  mutex := true;
}
