//#Unsafe
/*
 * Reveals bug in CFG Builder.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2025-01-22
 * 
 */

procedure proc() returns ()
modifies;
{
  var x : int;
  x := 0;
  while (*) {
      goto Label1;
      x := 0;
      Label1:
  }
  assert false;
}



  
