//#Safe
/*
 * Date: 2015-01-24
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * What is proven here?
 * If we increase the absolute value but retain the sign of operands, then
 * having a positive value is an invariant of the product.
 * 
 * We infer the (nonlinear) loop invariant (tmp1 * tmp2). This expression does
 * not occur in the program.
 *
 */

procedure main(in1, in2: int) returns (out1, out2: int)
requires in1 * in2 > 0;
ensures out1 * out2 > 0;
{
  var tmp1,tmp2: int;
  
  tmp1 := in1;
  tmp2 := in2;
  while (*) {
    if (tmp1 >= 0)  {
        tmp1 := tmp1 + 1;
    } else {
        tmp1 := tmp1 - 1;
    }
    if (tmp2 >= 0)  {
        tmp2 := tmp2 + 1;
    } else {
        tmp2 := tmp2 - 1;
    }
  }
  out1 := tmp1;
  out2 := tmp2;
}
