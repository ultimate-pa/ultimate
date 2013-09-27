/**
 * 
 */
package pea;

import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;


/**
 * @author OEA1LR
 *
 */
public class StrongVacuous {

	private HashSet<HashSet<CDD>> possiblyVacuous; 
	private HashSet<CDD> possVacuous;
	//list of formulas such that the pea this formula was generated from, 
    //gets vacuously satisfied if this formula holds in every state of the parallel product
    private HashSet<CDD> possibleVacuousMaker; //list of formulas, such that the pea this formulas was generated from, cannot be vacuously satisfied 
	//however it might lead to a vacuous satisfaction for other peas
    private HashSet<HashSet<CDD>> vacuous; //list of the formulae that are really vacuously satisfied
    
    public StrongVacuous() {
 
        this.possiblyVacuous = new HashSet<HashSet<CDD>>();
       
        this.possibleVacuousMaker = new HashSet<CDD>();
        this.vacuous = new HashSet<HashSet<CDD>>();
    }
    
    public void getVacuousAssignments(PhaseEventAutomata pea) throws IOException{

		Phase[] init = pea.getInit();
		int numberOfLocations = pea.getPhases().length;
		if (numberOfLocations <0) {
			System.out.println("ERROR: The pea is empty");
		}
		if (numberOfLocations ==1){
			CDD cdd = pea.getPhases()[0].getStateInvariant();
			
			Iterator vacuousMakerIterator = this.getPossibleVacuousMakerIterator();
			
			while (vacuousMakerIterator.hasNext()){
				CDD poss = (CDD) vacuousMakerIterator.next();
				if (cdd.implies(poss)){
					this.addToVacuous(cdd);
				}
				else if (poss.implies(cdd)){
					this.addToVacuous(poss);	
				}
			}
			this.addToPossVacuousMaker(cdd);

		}
		else{
			int numberOfInitStates = init.length;
			HashSet<CDD> possiblyVacuousPerReq = new HashSet<CDD>(numberOfInitStates); //note that for patterns we need only up to 5 initial states
			CDD cdd = CDD.TRUE;
			for (int i=0; i<numberOfInitStates; i++){
				Phase initState = init[i];
				//States that have a clockinvariant !=0 have to be left when the clock is expired
				//Thus such states cannot lead to a vacuous satisfaction
				if (initState.getClockInvariant() == CDD.TRUE){
					CDD vac = initState.getStateInvariant();
					possiblyVacuousPerReq.add(vac);
					cdd = cdd.or(vac);
				}
			}
			addToPossVacuous(cdd);
			this.addToPossiblyVacuous(possiblyVacuousPerReq);
		}
	}
    
    
	

	private void checkPossiblyVacuous(PhaseEventAutomata pea){
		 Phase[] phases = pea.getPhases();  
		 HashSet<HashSet<CDD>> vac = this.getPossiblyVacuous();		 
		 
		 Iterator vacIt = vac.iterator();
		 while(vacIt.hasNext()){
			 HashSet<CDD> vacuousPerReq = (HashSet<CDD>) vacIt.next();
			 Iterator vacPerReq = vacuousPerReq.iterator(); 
			 Boolean testGlobal = true;

			 for (int q=0; q<phases.length && testGlobal; q++){
				 Boolean testVacuous = false;
				 Phase a = phases[q];
				 CDD state = a.getStateInvariant();
				 while(vacPerReq.hasNext() && !testVacuous){
					 CDD formula = (CDD) vacPerReq.next();					 
					 if (state.and(formula) != CDD.FALSE){
						 testVacuous = true;
					 }
				 }
				 if (testVacuous == false){
					 testGlobal = false;
				 }
			 }
			 if (testGlobal == true){
				 this.addToVacuous(vacuousPerReq);
			 }
		 }
	 }
	 
	@SuppressWarnings("unchecked")
	private void checkPossibleVacuousMaker(PhaseEventAutomata pea){
		HashSet<CDD> possMaker = this.getPossibleVacuousMaker();
		HashSet<HashSet<CDD>> vacCandidate = this.getPossiblyVacuous();

		if (possMaker.isEmpty()||vacCandidate.isEmpty()){
			System.out.println("no possible vacuous formulas known OR no possible vacuous maker known");
		}
		else

		{	
			Boolean testVacuous = false;
			Iterator<CDD> possMakerIt = this.getPossibleVacuousMakerIterator();
			while(possMakerIt.hasNext() && !testVacuous){
				CDD formula = (CDD) possMakerIt.next();

				Iterator<HashSet<CDD>> possVacIt = vacCandidate.iterator();
				while (possVacIt.hasNext()){
					HashSet<CDD> possVacPerReq = possVacIt.next();
					Iterator<CDD> possVacPerReqIt = possVacPerReq.iterator();
					while (possVacPerReqIt.hasNext()){
					CDD state = possVacPerReqIt.next();
					if (formula.implies(state)){
						testVacuous = true;
						this.addToVacuous(state);
						this.addToVacuous(formula);
					}}
				}
			}


		}}
	
	public void checkVacuousSatisfiability(PhaseEventAutomata pea){
		 HashSet<HashSet<CDD>> vac = this.getPossiblyVacuous();
		 
		 if (vac.isEmpty()){
			 System.out.println("Before checking for vacuous satisfaction, you need to built-up the vacuous-vector");
		 }
		 else
			 {
			 checkPossiblyVacuous(pea);	 
			 checkPossibleVacuousMaker(pea);
			 }
	 }
	
	
			 
	 

	public HashSet<HashSet<CDD>> getPossiblyVacuous() {
		return this.possiblyVacuous;
	}

	private void addToPossVacuousMaker(CDD cdd) {
		this.possibleVacuousMaker.add(cdd);
		
	}

	private void addToVacuous(HashSet<CDD> cdd) {
		this.vacuous.add(cdd);		
	}
	
	private void addToVacuous(CDD cdd) {
		HashSet<CDD> cddSet = new HashSet<CDD>(1);
		cddSet.add(cdd);
		this.vacuous.add(cddSet);
		
	}

	
	private void addToPossiblyVacuous(HashSet<CDD> set) {
		this.possiblyVacuous.add(set);
		
	}

	public HashSet<CDD> getPossibleVacuousMaker() {
		// TODO Auto-generated method stub
		return this.possibleVacuousMaker;
	}
	
	private Iterator<CDD> getPossibleVacuousMakerIterator(){
		return this.possibleVacuousMaker.iterator();
	}

	private int getPossibleVacuousMakerLength() {
		// TODO Auto-generated method stub
		return this.possibleVacuousMaker.size();
	}
	
	public HashSet<HashSet<CDD>> getVacuous() {
		return vacuous;
	}
	
	private void addToPossVacuous(CDD cdd) {
		this.possVacuous.add(cdd);
		
	}
    
    
	
}
