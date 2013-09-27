package reqCheck;

import java.util.Vector;

import pea.CDD;
import pea.PhaseEventAutomata;

import PatternLanguage.PL_initiatedPattern;

//Checkt für Implikation A -> B, ob A auch mal wahr sein kann
//Checkt nur für pattern "it is always the case that if "A" holds then "B" holds as well"
//Checkt ausschließlich die InvariantPatterns mit Globally-Scope, 
//da für alle anderen Scopes der StronglyVacuousCheck funktioniert!!!!



public class WeakVacuous {
	
	public void checkInvariants(Vector<PL_initiatedPattern> reqs, PhaseEventAutomata pea){
		if (reqs.isEmpty()){
			System.out.println("ReqSet is empty");
			return;
		}
		else{
			Vector<CDD> preconds = this.getPreconds(reqs);
			for (int i=0; i< preconds.size(); i++){
				CDD precond = preconds.elementAt(i);
				if (! this.isSatisfiable(precond, pea)){
					System.out.println("Weakly vacuous satisfaction: The variable "+precond.toString()+" is never true");
				}
			}
			System.out.println("Weak vacuous satisfaction: checked");
			
		}
	}
	
	private Boolean isSatisfiable(CDD precond, PhaseEventAutomata pea){
		//Falls die StateInvariante jeder Location des pea der precondition widerspricht, dann kann precond nie gelten
		//--> Prüfe bis mind 1 Location gefunden, wo (precond && stateInv) erfüllbar bzw bis alle locations geprüft
		for (int i=0; i<pea.getNumberOfLocations(); i++){
			CDD stateInv = pea.getLocation(i).getStateInvariant();
			if (precond.and(stateInv) != CDD.FALSE){
				return true;
			}
		}
		return false;
	}
	
	private Vector<CDD> getPreconds(Vector<PL_initiatedPattern> reqs){
		Vector<CDD> preconds = new Vector();
		
		for (int i=0; i< reqs.size(); i++){
			//falls invariantPattern mit GloballyScope, dann nimm die Precondition in den Vector preconds auf
			if(	isInvariantPattern(reqs, i)){
				CDD precond = this.getPrecond(reqs, i);
				preconds.add(precond);
			}
		}
		return preconds;
	}
	
	private Boolean isInvariantPattern(Vector<PL_initiatedPattern> reqs, int i){
		if (reqs.get(i).getPatternClass().getPatternName().equals("invariantPattern") &&
				reqs.get(i).getScope().equals("Globally")){
			return true;
		}
		else 
			return false;
	}
	
	private CDD getPrecond(Vector<PL_initiatedPattern> reqs, int i){		
			CDD precond = reqs.get(i).getFirstNonLiteralTerminalCDD();
			return precond;
	}

}
