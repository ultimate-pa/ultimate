//#Terminating
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.06.2013
 *
 */

procedure main(x: int);

implementation main(x: int)
{
  if (x>=0) {
    call main(x - 1);
  }
  
}