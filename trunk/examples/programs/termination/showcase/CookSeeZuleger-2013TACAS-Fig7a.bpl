//#terminating
/*
 * Progam in Fig.7a of 
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 9.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y,d: int;

procedure main()
modifies x, y, d;
{
  while (x>0 && y>0 && d>0) {
    if (*) {
      x := x - 1;
      havoc d;
    } else {
      havoc x;
      y := y - 1;
      d := d - 1;
    }
  }
}