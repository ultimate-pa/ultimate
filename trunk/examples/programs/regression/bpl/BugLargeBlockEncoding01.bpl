//#Unsafe
/*
 * Date: 2012-07-27
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Bug with large block encoding
 * de.uni_freiburg.informatik.ultimate.logic.SMTLIBException: Undeclared function symbol (LBE45_0)
 *
 */

procedure proc() returns ()
{
  var tmp : int;
  assume tmp == 1;
    if (*) {
      tmp := tmp+1;
    }
    else {
      tmp := 0;
    }
  assert tmp != 0;
}
