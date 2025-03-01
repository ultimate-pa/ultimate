//#Unsafe
/*
 * Reveals bug in CFG Builder.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2025-03-01
 * 
 */

procedure proc() returns ()
modifies;
{
  var x : int;
  x := 0;
  if (*) {
      assume x !=0;
      Label1 { :auxiliary_label true} :
  } else {
  }
  assert false;
}



  
