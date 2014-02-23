//#terminating
/*
 * Progam in Fig.7b of 
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 9.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y,z: int;

procedure main()
modifies x, y, z;
{
  while (x>0 && y>0 && z>0) {
    if (*) {
      x := x - 1;
    } else if (*) {
      y := y - 1;
      havoc z;
    } else {
      z := z - 1;
      havoc x;
    }
  }
}