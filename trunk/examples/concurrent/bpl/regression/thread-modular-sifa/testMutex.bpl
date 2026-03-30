//#Safe
/*
*/

var mutex : int;
var crit : int;

procedure ULTIMATE.start()
modifies mutex, crit;
{
    mutex := 0;
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
    mutex := 0;
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
    mutex := 0;
}

procedure acquire_lock()
modifies mutex;
{
  if (mutex != 0) {
      assume 0 == 1;
  }
  mutex := 1;
}
