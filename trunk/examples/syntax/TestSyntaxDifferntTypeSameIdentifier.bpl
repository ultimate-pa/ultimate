//#SyntaxError
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 * Syntax error, same indentifier used for variables of differnt type
 * 
 */


procedure proc();

implementation proc()
{
  var x: bool;
  var x: int;
  var x: real;
  assume( x == true);
}




  
