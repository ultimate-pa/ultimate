//#Safe
var g : int;
var A : int;
var B : int;

procedure t_fun()
  modifies g, A, B;
{
  atomic { assume B == 0; B := 1; }
  atomic { assume A == 0; A := 1; }
  g := 17;
  atomic { A := 0; }
  atomic { B := 0; }
}

procedure main_thread()
  modifies g, A, B;
{
  atomic { assume A == 0; A := 1; }
  atomic { assume B == 0; B := 1; }
  g := 42;
  atomic { B := 0; }
  atomic { assume B == 0; B := 1; }
  assert g == 42;
  atomic { B := 0; }
  atomic { A := 0; }
}

procedure ULTIMATE.start()
  modifies g, A, B;
{
  g := 0;
  A := 0;
  B := 0;
  fork 1 t_fun();
  fork 2 main_thread();
}
