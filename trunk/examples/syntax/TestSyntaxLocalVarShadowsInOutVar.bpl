//#SyntaxError
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 19.4.2012
 * 
 * Syntax error local variable shadows invar and outvar.
 */


procedure proc(x: int) returns (y: int);

implementation proc(x: int) returns (y: int)
{
  var x,y: bool;
  assume( x == true);
  y := true;
}




  
