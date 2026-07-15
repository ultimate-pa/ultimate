//#Unsafe
var a : int;
var b : int;
var g : int;

procedure T1()
  modifies a, g;
{
  atomic { assume a == 0; a := 1; }
  g := 1;
  assert g == 1;
  atomic { a := 0; }
}

procedure T2()
  modifies b, g;
{
  atomic { assume b == 0; b := 1; }
  g := 2;
  atomic { b := 0; }
}

procedure ULTIMATE.start()
  modifies a, b, g;
{
  a := 0;
  b := 0;
  g := 0;
  fork 1 T1();
  fork 2 T2();
}
