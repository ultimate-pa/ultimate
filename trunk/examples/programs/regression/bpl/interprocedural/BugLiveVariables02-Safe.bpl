//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 29.10.2014
 * 
 * Bug relevant variables.
 *
 */

var g : int;


implementation ULTIMATE.start() returns ()
{
  assume g == 0;
  call proc();
}

implementation proc() returns ()
{
  call proc1();
  assert g == 0;
}

implementation proc1() returns ()
{
  assume true;
}



procedure proc() returns ();

procedure proc1() returns ();


procedure ULTIMATE.start() returns ();


