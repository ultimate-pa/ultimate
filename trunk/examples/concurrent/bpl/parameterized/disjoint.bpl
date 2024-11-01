//#Safe

procedure ULTIMATE.start()
{
  var x : int;
  while (x < 3) {
    x := x + 1;
    assert x != 0;
  }
}
