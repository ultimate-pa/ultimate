//#Safe
var m : int;
var g : int;

procedure T1()
  modifies m, g;
{
  var aux : int;
  atomic { assume m == 0; m := 1; }
  aux := 5;
  aux := aux + 1;
  g := 1;
  assert g == 1;
  atomic { m := 0; }
}

procedure T2()
  modifies m, g;
{
  var aux : int;
  atomic { assume m == 0; m := 1; }
  aux := 7;
  aux := aux + 1;
  g := 2;
  assert g == 2;
  atomic { m := 0; }
}

procedure ULTIMATE.start()
  modifies m, g;
{
  m := 0;
  g := 0;
  fork 1 T1();
  fork 2 T2();
}
