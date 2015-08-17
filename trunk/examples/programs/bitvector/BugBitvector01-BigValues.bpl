//#Unsafe
/* 
 * Bug in r14985. Value of satisfying assignment is parsed as long.
 * (Solution: Use BigInteger)
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-17
 */


var x:bv64;

procedure proc() returns ();

implementation proc() returns ()
{
  assert x != 9223372036854775807999bv64;
}

