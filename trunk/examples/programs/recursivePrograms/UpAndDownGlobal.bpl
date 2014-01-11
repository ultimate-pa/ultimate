//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: April 2010
 *
 * Recursive program which is correct with respect to the assert statement in
 * procedure Main.
 * In Order to proof correctness of we must be able to express invariants that
 * may refer to the condition of a global variable at the time of the procedure
 * call, like the "old" variables in boogie.
 * In this example we e.g. need that g = (old g) +1 is an invariant in
 * UpAndDownGlobal() before a call of UpAndDownGlobal().
 */

var g: int;

procedure Main(z: int);
free requires z>=0;
ensures g==z;
modifies g;

implementation Main(z: int)
{
  g:= z;
  call UpAndDownGlobal();
  assert g == z;
}

procedure UpAndDownGlobal() returns ();
modifies g;

implementation UpAndDownGlobal() returns ()
{
//  var x: int;

  g:=g+1;
  if (*) {
    call UpAndDownGlobal();
  }
  g:=g-1;
}
  
