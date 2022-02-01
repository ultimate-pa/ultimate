var valid, next, content : [int] int;

procedure ULTIMATE.start();
modifies valid, next, content;
implementation ULTIMATE.start() {
  var p, newListHead : int;
  assume valid[p] == 1;
  content[p] := 13;
  call newListHead := initList();
  assert content[p] == 13;
}

procedure initList() returns (res : int);
modifies valid, next, content;
implementation initList() returns (res : int) {
  var i, head : int;
  head := 0;
  while (*) {
    havoc i;
    assume valid[i] == 0;
    valid[i] := 1;
    next[i] := head;
    head := i;
    content[i] := 42;
  }
  res := head;
}
