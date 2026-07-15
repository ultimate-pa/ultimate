//#Unsafe
var mutex : int;
var data : int;

procedure ULTIMATE.start() returns ()
  modifies data, mutex;
{
  mutex := 0;
  data := 0;
  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
}

procedure thread1() returns ()
  modifies data, mutex;
{
  atomic { assume mutex == 0; mutex := 1; }
  data := data + 1;
  mutex := 0;
}

procedure thread2() returns ()
  modifies data, mutex;
{
  atomic { assume mutex == 0; mutex := 1; }
  data := data + 2;
  mutex := 0;
}

procedure thread3() returns ()
  modifies data, mutex;
{
  atomic { assume mutex == 0; mutex := 1; }
  if (data >= 3) {
    assert false;
  }
  mutex := 0;
}
