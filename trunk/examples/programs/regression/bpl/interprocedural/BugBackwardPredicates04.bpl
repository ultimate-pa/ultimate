//#Unsafe
/* Shows bug in BackwardPredicates in revision 12306.
 * Computed BP at beginning of proc is
 *     (distinct g m)
 * but should be 
 *     (= old(g) g)
 * Computed BP at end of proc is
 *     false
 * but should be
 *     (= old(g) m)
 * 
 * If you want that an assert in Ultimate fails you have to use 
 * ForwardPredicates and BackwardPredicates.
 * An assert fails because the ForwardPredicates do not imply the 
 * BackwardPredicates.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-09-07
 *
 */

var g : int;

implementation proc() returns ()
{
  if (*) {
    assume g != 3;
  } else {
  }
}

implementation main() returns ()
{
  assume old(g) == g;
  g := 7;
  call proc();
  assert (old(g) == 7);

}

procedure proc() returns ();
    modifies g;


procedure main() returns ();
    modifies g;
