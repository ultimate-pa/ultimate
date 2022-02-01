//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: April 2011
 *
 * Reduced version of GlobalUpAndDown.bpl
 */

var g: int;

procedure Main(z: int);
free requires g==z;
ensures g==z;
modifies g;

implementation Main(z: int)
{
  call GlobalUpAndDown();
}

procedure GlobalUpAndDown() returns ();
modifies g;

implementation GlobalUpAndDown() returns ()
{
  g := g;
  if (*) {
    call GlobalUpAndDown();
  }
}
  
