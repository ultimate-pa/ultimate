//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-07-24
 * 
 */

var a,b,c,d,e: real;


procedure main() returns ()
modifies b;
{
  assume (2.0 * c + 1.0 <= d + e) && (2.0 * b + 1.0 <= d + e) && (a <= b);
  havoc b;
  while (*) {
    //prevent large block encoding
  }
  assert (2.0 * c + 1.0 <= d + e) && 2.0 * a <= d + e - 1.0;
}


// eliminate [product__local__threadpooling_begin_0]
//(let ((.cse0 (+ product__local__threadpooling_end_0 product__local__threadpooling_i_1))) (and (<= (+ (* 2.0 product__local__threadpooling_end_1) 1.0) .cse0) (<= (+ (* 2.0 product__local__threadpooling_begin_0) 1.0) .cse0) (<= product__local__threadpooling_i_0 product__local__threadpooling_begin_0)))




  
