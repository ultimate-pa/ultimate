//#Safe
/* Bug in BlockEncoding in r10041.
 * Call-Return minimization crashes if call predecessor is dead code.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 24.10.2013
 *
 */

implementation proc() returns ()
{
}

implementation main() returns (#res : int)
{
    goto end;
  loc0:
    call proc();
  end:
}

procedure proc() returns ();
    modifies ;

procedure main() returns (#res : int);
    modifies ;



