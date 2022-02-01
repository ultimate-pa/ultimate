var g1, g2 : int;

axiom g1 == old(g1);

procedure proc()
requires old(old(g1)) > 0;
modifies g1, g2;
ensures g1 > old(7 * g1);
{
  var v: bool;
  g1 := old(g1 / old(old(f(g1)) + g2));
  g2 := 7 / old(7 - g2);
  v :=  (exists x: int :: old(x > g1 && g2 - 6 < 4));
  call sub(old(old(old(g2)) - 7));
}

procedure sub(x: int)
{
}

function f(x: int) returns (int);
axiom (forall x: int :: f(x) == old(g1 * x));

procedure realOld(x: int) returns (y: int)
modifies g2, g1;
modifies g2;
{
  y := old(x + 4 / old(g1));
}

procedure realOld2() returns ();
ensures g1 == old(g1);
modifies g1;

procedure noRealOld(x: int) returns (y: int) {
  y := old(x + 4 / old(g1));
}

procedure clearlyNoRealOld(x: int) returns (y: int) {
  y := 6 * old(x + 4 / old(x)) + 7;
}

procedure trickyNoRealOld()
modifies g1;
requires old(g1) > 0;
{
  // body
}

