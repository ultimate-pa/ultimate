//#cUnsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 05.04.2010
 *
 * Incorrect Concurrent Program.
 * Two context switches necessary to reach the error.
 */

 var g : int;

procedure ~init() returns();
modifies g;

implementation ~init()
{
   g := 0;
}

procedure Thread1()
modifies g;
{
  g := 0;

  while (*) {
    g := g + 1;
  }
  assert(g != -1);
}

procedure Thread2()
modifies g;
{
  g := -2;
}

