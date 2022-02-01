//#terminating
/*
 * Progam in Figure 3 of 
 * 2017arXiv - Brázdil,Chatterjee,Kučera,Novotný,Velan -  Efficient Algorithms for Checking Fast Termination in VASS
 *
 * Date: 2017-12-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y,z: int;

procedure main()
modifies x, y, z;
{
  while (z>0) {
    while (y > 0) {
      x := x + 2;
      y := y - 1;
    }
    while (x > 0) {
      x := x - 1;
      y := y + 2;
    }
    z := z - 1;
  }
}
