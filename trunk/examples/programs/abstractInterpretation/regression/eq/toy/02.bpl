//#Safe
/* 
 * (result checked via Automizer webinterface)
 *
 * Author: Alexander Nutz
 */
var valid : [int] bool;

procedure main();
modifies valid;

implementation main() {
  var p, q : int;
  var old_valid : [int] bool;
  
  old_valid := valid;

  call p := malloc();
  call q := malloc();

  call freemem(p);
  call freemem(q);

  assert valid == old_valid;
}

procedure malloc() returns (res : int);
modifies valid;
ensures old(valid)[res] == false;
ensures valid == old(valid)[res:=true];

procedure freemem(p : int);
modifies valid;
ensures valid == old(valid)[p:=false];


