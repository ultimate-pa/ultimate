//#Safe

var ctr : int;

procedure ULTIMATE.start()
free requires ctr == 0;
modifies ctr;
{
  while (*) {
    ctr := ctr + 1;
    assert ctr != 0;
    ctr := ctr - 1;
  }
}
