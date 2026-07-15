//#Safe
var g : int;
var A : int;
var B : int;
var C : int;

procedure t_fun()
  modifies B, C, g;
{
  atomic { assume B == 0; B := 1; }
  atomic { assume C == 0; C := 1; }
  g := 42;
  atomic { B := 0; }
  g := 17;
  atomic { C := 0; }
}

procedure main_thread()
  modifies A, B, C, g;
{
  atomic { assume A == 0; A := 1; }
  atomic { assume B == 0; B := 1; }
  atomic { assume C == 0; C := 1; }
  assert g == 17;
  atomic { A := 0; }
  atomic { B := 0; }
  atomic { C := 0; }
}

procedure ULTIMATE.start()
  modifies g, A, B, C;
{
  g := 17;
  A := 0;
  B := 0;
  C := 0;
  fork 1 t_fun();
  fork 2 main_thread();
}
