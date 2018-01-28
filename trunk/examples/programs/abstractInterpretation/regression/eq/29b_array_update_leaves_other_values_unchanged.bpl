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
 */
implementation main() {
  var p : int;
  var q : int;

  assume p != q;
  assume mem[p] == 2;

  mem[q] := 3;
  
  assert mem[p] == 2;
}

