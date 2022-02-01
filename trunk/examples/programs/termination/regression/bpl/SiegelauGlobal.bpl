//#Terminating
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 17.06.2013
 *
 */

var g: int;

procedure main();
modifies g;

implementation main()
{
  if (g>=0) {
    g := g - 1;
    call main();
  }
  
}