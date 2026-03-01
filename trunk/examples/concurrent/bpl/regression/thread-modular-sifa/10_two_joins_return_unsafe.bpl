//#Unsafe

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
  var a : int;
  var a_old : int;

  fork 0 foo();
  join 0 assign a;

  fork 1 foo();
  a_old := a;
  join 1 assign a;

  assert a_old == a;
}

procedure foo() returns (res : int)
{
  var y : int;
  res := y;
}
