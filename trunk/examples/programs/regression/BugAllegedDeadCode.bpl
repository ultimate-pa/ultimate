//#Unsafe
/*
 * Date: 16.06.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Reveals bug in Preprocessor in r6233.
 * The label Label1 is considered as deadCode
 */

//var x: int;

procedure proc()
{
  if (*) {
    goto Label1;
  }
  goto Label2;
  if (*) {
    Label1:
    assert(false);
  }
  Label2:
}

