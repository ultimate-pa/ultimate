//#Unsafe
var g : int;
var A : int;
var D : int;

procedure t_fun()
  modifies A, D, g;
{
  atomic { assume D == 0; D := 1; }
  atomic { assume A == 0; A := 1; }
  g := 17;
  atomic { A := 0; }
  atomic { D := 0; }
}

procedure main_thread()
  modifies A, D, g;
{
  atomic { assume D == 0; D := 1; }
  atomic { assume A == 0; A := 1; }
  atomic { D := 0; }
  assert g != 0;
}

procedure ULTIMATE.start()
  modifies g, A, D;
{
  g := 0;
  A := 0;
  D := 0;
  fork 1 t_fun();
  fork 2 main_thread();
}
