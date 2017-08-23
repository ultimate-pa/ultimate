//#Safe
/* 
 * (result checked via Automizer webinterface)
 *
 * Author: Alexander Nutz
 */
var mem : [int] int;
var valid : [int] bool;

procedure main();
modifies valid, mem;

/*
 * Automizer derived the following contract:
 * 12 == mem[p] && (exists foo_q : int :: mem[foo_q] == 13)
 */
implementation main() {
  var p : int;
  call p := malloc();
  mem[p] := 12;
  call foo();
  assert mem[p] == 12;
}

procedure foo();
modifies valid, mem;

/*
 * Automizer derived the following contract:
 * (exists foo_q : int :: !old(valid)[foo_q] && mem == old(mem)[foo_q := 13])
 */
implementation foo() {
  var q : int;
  call q := malloc();
  mem[q] := 13;
  call freemem(q);
}

procedure malloc() returns (res : int);
modifies valid;
ensures old(valid)[res] == false;
ensures valid == old(valid)[res:=true];

procedure freemem(p : int);
modifies valid;
ensures valid == old(valid)[p:=false];


