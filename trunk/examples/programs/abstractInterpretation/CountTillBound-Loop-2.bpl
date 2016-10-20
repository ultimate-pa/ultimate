//#Safe
/*
 * Ultimate Automizer is unable to prove safety efficiently because
 * (in r9676) we get the following interpolants.
 * [(<= _x_-1 0), (<= _x_1 1), (<= _x_2 2), false]
 * 
 * Explanation:
 * Consider the following error trace.
 * st1: x := 0;
 * st2: y := 42;
 * st3: assume x < 100
 * st4: x := x + 1;
 * st5: assume y > 0;
 * st6: assume x >= 100;
 * st7: assume x != 100 || y !=42;
 * 
 * This trace is infeasible for two reasons.
 * It seems however that the constradiction beween the three statements
 * st1, st4 and st6
 * is the "favorite" reasons of SMT solvers. Probably because it allows
 * the solver to "talk" about a single variable
 * 
 * Date: 23.09.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x,y: int;

procedure main()
modifies x,y;
{
  x := 0;
  y := 42;
  while (x < 100) {
    x := x + 1;
    while(y <= 0)
    {
		y := 42;
    }
  }

  assert(x == 100 && y == 42);
}