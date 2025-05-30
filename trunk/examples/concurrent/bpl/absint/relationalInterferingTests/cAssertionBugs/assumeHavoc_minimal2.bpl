var mem : int;

procedure read_int() returns (out : int)
  modifies;
{
  out := 1;
  return;
}

procedure ULTIMATE.start()
  modifies mem;
{
  var t : int;
  mem := 0;

Loop:
  call t := read_int();
  goto Loop;
}
