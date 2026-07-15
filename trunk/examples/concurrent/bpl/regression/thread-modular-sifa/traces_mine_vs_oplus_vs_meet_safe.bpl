//#Safe
var g : int;
var A : int;
var B : int;
var C : int;

procedure t_fun()
  modifies g, A, B, C;
{
  atomic { assume A == 0; A := 1; }
  atomic { assume C == 0; C := 1; }
  atomic { assume B == 0; B := 1; }
  g := 5;
  atomic { B := 0; }
  atomic { assume B == 0; B := 1; }
  g := 0;
  atomic { B := 0; }
  atomic { C := 0; }
  atomic { A := 0; }
}

procedure main_thread()
  modifies A, B, C;
{
  atomic { assume B == 0; B := 1; }
  atomic { assume C == 0; C := 1; }
  assert g == 0;
  atomic { C := 0; }
  atomic { B := 0; }
  atomic { assume A == 0; A := 1; }
  atomic { assume B == 0; B := 1; }
  assert g == 0;
  atomic { B := 0; }
  atomic { A := 0; }
}

procedure ULTIMATE.start()
  modifies g, A, B, C;
{
  g := 0;
  A := 0;
  B := 0;
  C := 0;
  fork 1 t_fun();
  fork 2 main_thread();
}
