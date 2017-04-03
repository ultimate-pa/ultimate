//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 5.10.2013
 * 
 * Variant of WrongBFS that is safe.
 * If the identifier "ULTIMATE.start" is used, our tool considers only program
 * executions starting with this procedure.
 */

var g: int;

procedure ULTIMATE.start();
modifies g;

implementation ULTIMATE.start()
{
  g:= 0;
  call u();
  assert g != 0;
}

procedure u() returns ();
modifies g;

implementation u() returns ()
{
  g:=g+1;
  if (g <= 1) {
    call u();
  }
}
 
