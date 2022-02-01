//#SyntaxError
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 * 
 * Syntax error
 */


procedure proc(x: int) returns (x: bool);

implementation proc(x: int) returns (x: bool)
{
  assume( x == 42);
}




  
