//#terminating
/*
 * Progam in Fig.3 of 
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 9.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y: int;

procedure main()
modifies x, y;
{
  while (x>0 && y>0) {
    if (*) {
      x := x - 1;
    } else {
      havoc x;
      y := y - 1;
    }
  }
}