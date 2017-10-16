//#Safe
/* 
 * (result checked via Automizer webinterface)
 *
 * Author: Alexander Nutz
 */
var mem : [int, int] int;
var valid : [int] bool;

procedure main();
modifies valid, mem;

/*
 */
implementation main() {
  var p.base, p.offset : int;
  var q.base, q.offset : int;

  call p.base, p.offset := malloc();
  mem[p.base, p.offset] := 12;

  call q.base, q.offset := malloc();
  mem[q.base, q.offset] := 13;
  call freemem(q.base, q.offset);
  havoc q.base;

  assert mem[p.base, p.offset] == 12;
}

procedure malloc() returns (base, offset : int);
modifies valid;
ensures old(valid)[base] == false;
ensures valid == old(valid)[base:=true];
ensures offset == 0;

procedure freemem(base, offset : int);
modifies valid;
ensures valid == old(valid)[base:=false];


