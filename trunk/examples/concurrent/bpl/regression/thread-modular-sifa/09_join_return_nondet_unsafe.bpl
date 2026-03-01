//#Unsafe

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
  var a : int;
  a := 0;

  fork 0 foo();
  join 0 assign a;

  assert a == 0;
}

procedure foo() returns (res : int)
{
  var y : int;
  res := y;
}
