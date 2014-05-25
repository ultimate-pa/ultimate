//#Safe
/* Shows bug in BackwardPredicats in revision 11643.
 * Maybe only reproduceable if TransFormulas are not converted to CNF
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 24.5.2014
 *
 */

implementation doNothing() returns ()
{
  return;
}

implementation main() returns ()
{
  var a,b,c : bool;

  a := true;
  b := true;
  if (c) {
    a := false;
  } else {
    b := false;
  }
  if (false) {
  } else {
    call doNothing();
  }
  assert (a || b);

}

procedure doNothing() returns ();
    modifies ;


procedure main() returns ();
    modifies ;
