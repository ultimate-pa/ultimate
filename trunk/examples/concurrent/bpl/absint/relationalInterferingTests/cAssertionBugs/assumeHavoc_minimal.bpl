var mem : int;

procedure read_int() returns (out : int)
  modifies;
{
  out := mem;
  return;
}

procedure {:entrypoint} ULTIMATE.start()
  modifies mem;
{
  var t : int;
  mem := 0;

Loop:
  call t := read_int();
  if (t == 0) {
    assume 0 == t % 4294967296;
    havoc  t;
  }

  goto Loop;
}

