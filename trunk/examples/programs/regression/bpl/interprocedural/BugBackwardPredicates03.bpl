//#Safe
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
 * Date: 2014-09-04
 *
 */

var g,m : int;

implementation proc() returns ()
{
    assume g == m;
}

implementation main() returns ()
{
  assume g != m;
  call proc();
  assert (false);

}

procedure proc() returns ();
    modifies g;


procedure main() returns ();
    modifies g;
