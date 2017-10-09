var valid, next, content : [int] int;

procedure ULTIMATE.start();
modifies valid, next, content;
implementation ULTIMATE.start() {
  var p, newListHead : int;
  call newListHead := initList();
}

procedure initList() returns (res : int);
modifies valid, next, content;
implementation initList() returns (res : int) {
  var i, j: int;
  assume valid[j] == 1;
  while (*) {
    havoc i;
    assume valid[i] == 0;
    valid[i] := 1;
    assert i != j;
  }
}
