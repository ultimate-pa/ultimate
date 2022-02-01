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
  var i : int;
  while (*) {
    havoc i;
    assume valid[i] == 0;
    valid[i] := 1;
    content[i] := 42;
  }
}
