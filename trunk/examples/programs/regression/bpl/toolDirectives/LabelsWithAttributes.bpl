//#Safe
// Author: 	matthias.heizmann@iste.uni-stuttgart.de
// Date: 2025-01-03
//
// Test for our Boogie extension that allows labels to have attributes.

procedure proc() returns ()
modifies;
{
  var x : int;
  assume x == 0;
  MyLabel  { :keyA "valueA1", "valueA2"} { :auxiliary_label } { :keyB "valueB"} :
  assert(x == 0);

}



