//#Safe
/*
 * Reveals but in CFG Builder.
 * 
 * Old Algorithm
 * - Create node for Label1
 * - Create node for Label2, merge Label1 into Label2, let map for Label1 point to node of Label2
 * - Create node for Label3, merge Label2 into Label3, let map for Label2 point to node of Label3
 * 
 * When the goto is processed it becomes and edge that points to the node for Label2 which has no successors.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-12-01
 * 
 */

procedure proc() returns ()
modifies;
{
  var x : int;
  assume x == 0;
  Label1:
  Label2:
  Label3:
  assert(x == 0);
  x := 1;
  goto Label1;
}



  
