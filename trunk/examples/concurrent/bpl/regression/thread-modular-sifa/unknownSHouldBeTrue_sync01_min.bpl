//#Safe
var num   : int;
var mutex : int;
var d1    : int;
var d2    : int;

procedure thread1()
  modifies num, mutex, d1;
{
  var race: int;
  atomic { assume mutex == 0; mutex := 1; }
  race := num;
  assert race == num;
  assume num == 0; num := num + 1; mutex := 0; d1 := 1;
}

procedure thread2()
  modifies num, mutex, d2;
{
  var race: int;
  atomic { assume mutex == 0; mutex := 1; }
  race := num;
  assert race == num;
  assume num > 0; num := num - 1; mutex := 0; d2 := 1;
}

procedure ULTIMATE.start()
  modifies num, mutex, d1, d2;
{
  num   := 1;
  mutex := 0;
  d1    := 0;
  d2    := 0;

  fork 1 thread1();
  fork 2 thread2();
}
