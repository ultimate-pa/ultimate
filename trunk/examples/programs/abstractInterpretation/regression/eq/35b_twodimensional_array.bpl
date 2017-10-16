//#Safe
/* 
 * (result checked via Automizer webinterface)
 *
 * Author: Alexander Nutz
 */
var mem : [int, int] int;
var valid : [int] int;

procedure main();
modifies valid, mem;

/*
 */
implementation main() {
  var p.base, p.offset : int;
  var q.base, q.offset : int;

  assume valid[p.base] == 0;
  valid[p.base] := 1;

  mem[p.base, p.offset] := 12;

  assume valid[q.base] == 0;
  valid[q.base] := 1;

  mem[q.base, q.offset] := 7;

  assert mem[p.base, p.offset] == 12;
}


