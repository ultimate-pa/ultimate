//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 13.5.2012 (Muttertag!)
 * Leads to the following error in r6054
 * de.uni_freiburg.informatik.ultimate.logic.SMTLIBException: Unexpected Exception while parsing
 */
procedure proc();

implementation proc()
{
  assume (forall i : int :: i == 0);
  assert (0 == 0);
}





  
