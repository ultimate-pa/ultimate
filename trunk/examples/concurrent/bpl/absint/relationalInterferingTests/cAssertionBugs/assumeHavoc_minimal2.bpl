procedure read_int() returns (out : int)
  modifies;
{
  out := 1;
  return;
}

procedure ULTIMATE.start()
{
  var t : int;

  while (true) {
    call t := read_int();
  }
}
