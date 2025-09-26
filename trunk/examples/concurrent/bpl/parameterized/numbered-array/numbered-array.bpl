//#Safe

var a : [int]int;
var ctr : int;

procedure ULTIMATE.start()
modifies ctr, a;
{
  var id : int;
  atomic {
    id := ctr;
    ctr := ctr + 1;
  }

  a[id] := id;
  assert a[id] == id;
}
