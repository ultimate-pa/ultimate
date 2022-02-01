//#Safe
/* Date: 2015-04-19
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */

var y: int;

procedure main()
modifies y;
{
  assume y >= 5;
  while (*) {
  }
  assert(y > 4);
}

