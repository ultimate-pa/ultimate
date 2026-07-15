//#Safe
var g2 : int;
var mutex1 : int;
var mutex2 : int;
var global_lock : int;

procedure t2_fun()
  modifies g2, mutex2, global_lock;
{
  atomic { assume mutex2 == 0; mutex2 := 1; }
  atomic { assume global_lock == 0; global_lock := 1; }
  g2 := g2 + 1;
  atomic { global_lock := 0; }
  atomic { assume global_lock == 0; global_lock := 1; }
  g2 := g2 - 1;
  atomic { global_lock := 0; }
  atomic { mutex2 := 0; }
}

procedure main_thread()
  modifies mutex1, mutex2, global_lock;
{
  atomic { assume mutex1 == 0; mutex1 := 1; }
  atomic { assume global_lock == 0; global_lock := 1; }
  assert 0 <= g2;
  assert g2 <= 1;
  atomic { global_lock := 0; }
  atomic { assume mutex2 == 0; mutex2 := 1; }
  atomic { assume global_lock == 0; global_lock := 1; }
  assert g2 == 0;
  atomic { global_lock := 0; }
  atomic { mutex2 := 0; }
  atomic { mutex1 := 0; }
}

procedure ULTIMATE.start()
  modifies g2, mutex1, mutex2, global_lock;
{
  g2 := 0;
  mutex1 := 0;
  mutex2 := 0;
  global_lock := 0;
  fork 1 t2_fun();
  fork 2 main_thread();
}
