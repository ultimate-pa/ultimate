//#cUnsafe
/*
 * test
 *
 */

 var critical : int;
 var g : int;

procedure ~init() returns();
modifies critical;

implementation ~init()
{
   critical := 0;
}



procedure Thread1();
modifies g;

implementation Thread1()
{
  var x, y: int;

  x := 0;
  y := 0;
  g := 0;

  while (*) {
    x := x + 1;
    g := g + 1;
  }

  assert(x != -1);
  assert(y != -1);
  assert(g != -1);
}



procedure Thread2();
modifies g;

implementation Thread2()
{
  var a, b: int;

  a := 0;
  b := 0;

  while (*) {
    a := a + 1;
  }
//  g := -2;

  assert(a != -1);
  assert(b != -1);
}

