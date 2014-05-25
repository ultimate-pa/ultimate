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
  var c : int;
  var y : int;
  var x : int;
  var b : bool;

  c := 0;
  if (b) {
    c := 1;
    x := y;
  } 
  if (false) {
  } else {
    call doNothing();
  }
  assume (y > 0);
  assume (c == 1);
  assert (0 <= x);

}

procedure doNothing() returns ();
    modifies ;


procedure main() returns ();
    modifies ;
