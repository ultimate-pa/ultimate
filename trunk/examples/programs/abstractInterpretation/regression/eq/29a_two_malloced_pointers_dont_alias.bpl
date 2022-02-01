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
  var q : int;

  call p := malloc();
  call q := malloc();

  assert p != q;
}

procedure malloc() returns (res : int);
modifies valid;
ensures old(valid)[res] == false;
ensures valid == old(valid)[res:=true];

