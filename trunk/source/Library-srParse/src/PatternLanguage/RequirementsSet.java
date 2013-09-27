package PatternLanguage;

import java.util.Vector;

import pea.CDD;
import pea.PhaseEventAutomata;

/*
 **
 * The class <code>RequirementsSet</code> stores Requirements given as Strings in Pattern language. 
 * The variables the requirements are speaking about are stored in "variables". The variables shall be given with the 
 * initialization of this class.
 * 
 * It provides a method to transform these Requirements into DC formulas (then stored in <code>RequirementsSetDC</code>)
 * 
 * 
 * @author Amalinda Oertel
 * April 2010
 * 
 * @see J2UPPAALWriter
 */

public class RequirementsSet {
	
	private Vector<String> requirementsSet;
	private Vector<PL_initiatedPattern> requirementsSetInitPattern;
	

	private Vector<CDD> variables;
	

	private boolean isInconsistent;
	
	public RequirementsSet(Vector<CDD> variables){
		this.variables = variables;
		this.requirementsSet = new Vector();
		this.requirementsSetInitPattern = new Vector();
		this.setInconsistent(false);
	}
	
	public int getReqSetSize(){
		return requirementsSet.size();
	}
	
	public void addToReqSet(String requirement){
		PL_initiatedPattern req = new PL_initiatedPattern(requirement, variables);
		if (req.patternRecognized()){
			requirementsSet.addElement(requirement);
			requirementsSetInitPattern.addElement(req);
		}
	}
	
	public Vector<PhaseEventAutomata> transformToPEA(){
		PL_Pattern2Logic toLogic = new PL_Pattern2Logic();
		Vector<PhaseEventAutomata> reqAsPEA = new Vector();
		
		for (int i=0; i<this.getReqSetSize(); i++){
			PL_initiatedPattern reqP = requirementsSetInitPattern.elementAt(i);
		 	toLogic.transformPatternToLogic(reqP, "DC");
		 	PhaseEventAutomata pea = toLogic.getLogicPEA("DC");
		 	reqAsPEA.addElement(pea);
		}
		return reqAsPEA;
	}
	
	public String getRequirementString(int i){
		if (i> this.getReqSetSize()){
			return "ERROR: Index out of Bound";
		}
		else return requirementsSet.elementAt(i);
	}
	
	public PL_initiatedPattern getRequirementInitiatedPattern(int i){
		return requirementsSetInitPattern.elementAt(i);
	}	

	public void setRequirementsSet(Vector<String> requirementsSet) {
		for (int i=0; i< requirementsSet.size(); i++){
			this.addToReqSet(requirementsSet.elementAt(i));
		}
		
	}

	public Vector<String> getRequirementsSet() {
		return requirementsSet;
	}
	
	public Vector<PL_initiatedPattern> getRequirementsSetInitPattern() {
		return requirementsSetInitPattern;
	}

	public void setInconsistent(boolean isInconsistent) {
		this.isInconsistent = isInconsistent;
	}

	public boolean isInconsistent() {
		return isInconsistent;
	}
	
	public Vector<CDD> getVariables() {
		return variables;
	}

}
