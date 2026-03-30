var v   : int;
var mem : int;
var race: int;

procedure __VERIFIER_atomic_begin()
  modifies v, mem, race;
{ }

procedure __VERIFIER_atomic_end()
{ }

procedure T1()
  modifies v, race, mem;
{
  call __VERIFIER_atomic_begin();
  havoc v;
  race := 0;
  call __VERIFIER_atomic_end();
}

procedure TX()
  modifies mem, race, v;
{
  call __VERIFIER_atomic_begin();
  assert race == 0;
  race  := 3;
  mem   := 88;
  race  := 0;
  call __VERIFIER_atomic_end();
}

procedure TY()
  modifies mem, race, v;
{
  call __VERIFIER_atomic_begin();
  assert race == 0;
  race  := 6;
  mem   := 89;
  race  := 0;
  call __VERIFIER_atomic_end();
}

procedure ULTIMATE.start()
  modifies v, mem, race;
{
  fork 1 T1();
  fork 2 TX();
  fork 3 TY();
}

