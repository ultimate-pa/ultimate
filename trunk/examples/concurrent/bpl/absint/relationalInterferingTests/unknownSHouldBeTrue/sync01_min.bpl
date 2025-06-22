var num   : int;
var mutex : bool;
var d1    : bool;
var d2    : bool;

procedure thread1()
  modifies num, mutex, d1;
{
  var race: int;
  atomic { assume mutex == false; mutex := true; }
  race := num;
  assert race == num;
  assume num == 0; num := num + 1; mutex := false; d1 := true;
}

procedure thread2()
  modifies num, mutex, d2;
{
  var race: int;
  atomic { assume mutex == false; mutex := true; }
  race := num;
  assert race == num;
  assume num > 0; num := num - 1; mutex := false; d2 := true;
}

procedure ULTIMATE.start()
  modifies num, mutex, d1, d2;
{
  num   := 1;
  mutex := false;
  d1    := false;
  d2    := false;

  fork 1 thread1();
  fork 2 thread2();
}

