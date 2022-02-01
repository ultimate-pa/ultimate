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
  var p : int;
  assume valid[p] == 1;
  content[p] := 13;
  call initList();
  assert content[p] == 13;
}

procedure initList();
modifies valid, content;
implementation initList() {
  var i,j, k : int;

  assume valid[i] == 0;
  valid[i] := 1;
  content[i] := 42;

  assume valid[j] == 0;
  valid[j] := 1;
  content[j] := 42;

  assume valid[k] == 0;
  valid[k] := 1;
  content[k] := 42;
}
