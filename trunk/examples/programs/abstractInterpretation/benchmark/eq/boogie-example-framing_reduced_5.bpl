//#Safe
/*
 * (result checked via Automizer web interface on 07.10.2017)
 *
 * author: nutz@informatik.uni-freiburg.de
 */
var valid, content : [int] int;

procedure ULTIMATE.start();
modifies valid, content;
implementation ULTIMATE.start() {
  var p, i : int;
  assume valid[p] == 1;
  content[p] := 13;
  call initList();
  assert content[p] == 13;
}

procedure initList();
modifies valid, content;
implementation initList() {
  var i, j : int;

  havoc i;
  assume valid[i] == 0;
  valid[i] := 1;
  content[i] := 42;

  havoc i;
  assume valid[i] == 0;
  valid[i] := 1;
  content[i] := 42;

  havoc i;
  assume valid[i] == 0;
  valid[i] := 1;
  content[i] := 42;
}
