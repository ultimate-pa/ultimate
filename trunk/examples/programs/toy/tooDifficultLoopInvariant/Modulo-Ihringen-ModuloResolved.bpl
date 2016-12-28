//#Safe
/*
 * Variant of Modulo-Ihringen.bpl were the preprocessing of modulo
 * operations was applied in advance.
 * 
 * Date: 2016-12-27
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  var remainderAuxVar, quotientAuxVar: int;
  
  x := 8;

  while (*) {
    // break LBE
  }
  
  // x := x % 7;
  assume (0 <= remainderAuxVar);
  assume (remainderAuxVar < 7);
  assume (x == quotientAuxVar * 7 + remainderAuxVar);
  x := remainderAuxVar;
  
  while (*) {
    // break LBE
  }

  assert (x <= 1);

} 
