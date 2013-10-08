//#rTerminationDerivable
/*
 * Date: 2013-08-24
 *
 * Has the lexicographic ranking function f(x1, x2, x3) = <x_2, x_3>.
 *
 * From Amir Ben-Amram
 */

procedure main() returns (x1 : int, x2 : int, x3 : int)
{
  while (x1 >= 0 && x2 >= 0 && x3 >= -x1) {
    x2 := x2 - x1;
    x3 := x3 + x1 - 2;
  }
}

